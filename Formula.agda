open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Equality

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ}
      -------
    → zero ≤ n

  s≤s : {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

data _⊔_is_ (m n p : ℕ) : Set where
  left⊔ : m ≤ n → p ≡ n → m ⊔ n is p
  right⊔ : n ≤ m → p ≡ m → m ⊔ n is p

≤total : (m n : ℕ) → Total m n
≤total zero n = forward z≤n
≤total (suc m) zero = flipped z≤n
≤total (suc m) (suc n) with ≤total m n
...                       | forward m≤n = forward (s≤s m≤n)
...                       | flipped n≤m = flipped (s≤s n≤m)

_⊔_ : (m n : ℕ) → ℕ
zero ⊔ zero = zero
zero ⊔ suc n = suc n
suc m ⊔ zero = suc m
suc m ⊔ suc n = suc (m ⊔ n)

m⊔m≡m : {m : ℕ} → m ⊔ m ≡ m
m⊔m≡m {zero} = refl
m⊔m≡m {suc m} rewrite m⊔m≡m {m} = refl

⊔-is-⊔ : (m n : ℕ) → m ⊔ n is (m ⊔ n)
⊔-is-⊔ zero zero = left⊔ z≤n refl
⊔-is-⊔ zero (suc n) = left⊔ z≤n refl
⊔-is-⊔ (suc m) zero = right⊔ z≤n refl
⊔-is-⊔ (suc m) (suc n) with ⊔-is-⊔ m n
⊔-is-⊔ (suc m) (suc n)    | left⊔ m≤n p with m ⊔ n
⊔-is-⊔ (suc m) (suc n)    | left⊔ m≤n refl | _ = left⊔ (s≤s m≤n) refl
⊔-is-⊔ (suc m) (suc n)    | right⊔ n≤m p with m ⊔ n
⊔-is-⊔ (suc m) (suc n)    | right⊔ n≤m refl | _ = right⊔ (s≤s n≤m) refl

m≤n∧n≤m→m≡n : {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
m≤n∧n≤m→m≡n z≤n z≤n = refl
m≤n∧n≤m→m≡n (s≤s m≤n) (s≤s n≤m) rewrite m≤n∧n≤m→m≡n m≤n n≤m = refl

⊔-≡ : (m n : ℕ) {p q : ℕ} → m ⊔ n is p → m ⊔ n is q → p ≡ q
⊔-≡ m n (left⊔ _ refl) (left⊔ _ refl) = refl
⊔-≡ m n (left⊔ m≤n refl) (right⊔ n≤m refl) = m≤n∧n≤m→m≡n n≤m m≤n
⊔-≡ m n (right⊔ n≤m refl) (left⊔ m≤n refl) = m≤n∧n≤m→m≡n m≤n n≤m
⊔-≡ m n (right⊔ _ refl) (right⊔ _ refl) = refl

infix 4 _≤_

data OpenFormula : ℕ → Set where
  var : (n : ℕ) → OpenFormula n
  ∩_ : ∀{m} → OpenFormula (suc m) → OpenFormula m
  ∪_ : ∀{m} → OpenFormula (suc m) → OpenFormula m
  α : ∀{m n} → OpenFormula m → OpenFormula n → OpenFormula (m ⊔ n)
  ν : ∀{m n} → OpenFormula m → OpenFormula n → OpenFormula (m ⊔ n)
  ι : ∀{m n} → OpenFormula m → OpenFormula n → OpenFormula (m ⊔ n)
  _∧_ : ∀{m n p} → .{m⊔n≡p : m ⊔ n ≡ p} → OpenFormula m → OpenFormula n → OpenFormula p
  _∨_ : ∀{m n p} → .{m⊔n≡p : m ⊔ n ≡ p} → OpenFormula m → OpenFormula n → OpenFormula p
  _⇒_ : ∀{m n p} → .{m⊔n≡p : m ⊔ n ≡ p} → OpenFormula m → OpenFormula n → OpenFormula p

formula-cong : ∀{m n} → m ≡ n → OpenFormula m ≡ OpenFormula n
formula-cong {m} refl = refl

test0 : ∀{m} → OpenFormula (suc m) → OpenFormula m
test0 {m} u = ∪ θ
  where θ : OpenFormula (suc m)
        θ rewrite (m⊔m≡m {suc m}) = {! u ⇒ u !}

test1 : ∀{m} → OpenFormula (suc m) → OpenFormula m
test1 {m} u = ∩ (_⇒_ {m⊔n≡p = m⊔m≡m {suc m}} u u)

test2 : ∀{m n} → OpenFormula (suc m) → OpenFormula (suc n) → OpenFormula ((m ⊔ n) ⊔ (m ⊔ n))
test2 {m} {n} u v = (∩ (u ⇒ v)) ⇒ (∩ u) ⇒ (∪ v)

test3 : ∀{m n} → OpenFormula (suc m) → OpenFormula (suc n) → OpenFormula (m ⊔ n)
test3 {m} {n} u v = _⇒_ {m⊔n≡p = m⊔m≡m {m ⊔ n}} (∩ (u ⇒ v)) ((∩ u) ⇒ (∪ v))

infixl 9 _∧_
infixr 10 _⇒_
infixl 11 _∨_

Formula : Set
Formula = OpenFormula zero

x : OpenFormula 1
x = var 1

y : OpenFormula 2
y = var 2

∩xx : Formula
∩xx = ∩ x

∩xy : OpenFormula 1
∩xy = ∩ y

∩x∪yxιy : OpenFormula zero
∩x∪yxιy = ∩ ∩ ((var 1) ⇒ (var 2))

xαx : OpenFormula 1
xαx = x ∧ x

xα∩xx : OpenFormula 1
xα∩xx = x ∧ ∩xx

∩xxαx : OpenFormula 1
∩xxαx = ∩xx ∧ x

∩xxα∩xx : Formula
∩xxα∩xx = ∩xx ∧ ∩xx

