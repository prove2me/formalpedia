-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_lemma_2_2
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.lemma_2_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:56:59.512683+00:00
-- url     : https://prove2.me/theorems/be179f65-ea7b-4128-a0ca-bb59cff1644d
-- title:
--   Unique generator-fixing reversal anti-isomorphism
-- statement:
--   Let $r\ge1$ and let $R$ be a commutative unital ring. Fix units $q,\delta,\rho,u_1,\ldots,u_r$, with $\delta=q-q^{-1}$, and moments $\omega_a\in R$ for $a\in\mathbb Z$, with $\omega_0=1-\delta^{-1}(\rho-\rho^{-1})$. Write $B_{r,n}$ for the unital algebra with all relations of Definition 2.1; $T_i,E_i,X_j^{\pm1}$ denote its specified generators. Neither $\omega_0\ne0$ nor its invertibility is assumed.
--
--   For $n\ge1$, there exists a unique $R$-linear bijection $*:B_{r,n}\to B_{r,n}$ satisfying
--   $$ (ab)^*=b^*a^*,\qquad T_i^*=T_i,\quad E_i^*=E_i,\quad X_j^*=X_j\qquad(1\le i<n,\ 1\le j\le n).$$
--
--   This identifies the canonical reversal of products in the presented algebra. Its existence is a conclusion, not a hypothesis.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 3, Lemma 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section Presentation

variable {R : Type*} [CommRing R] {r : ℕ} (P : Ground R r) (n : ℕ)

local notation "t" => ruiXuFreeT R n

local notation "e" => ruiXuFreeE R n

local notation "x" => ruiXuFreeX R n

local notation "c" => algebraMap R (FreeAlgebra R (RuiXuLetter n))

/-- Lemma 2.2, PDF p.3: unique R-linear multiplicative-order-reversing
bijection fixing all named generators. The existence is the descent of word
reversal; no anti-involution is supplied as a hypothesis. -/
theorem lemma_2_2 (hn : 0 < n) :
    ∃! star : RuiXuBMW P n →ₗ[R] RuiXuBMW P n,
      Function.Bijective star ∧
      (∀ a b, star (a * b) = star b * star a) ∧
      (∀ i, 1 ≤ i → i < n → star (T P n i) = T P n i ∧ star (ruiXuE P n i) = ruiXuE P n i) ∧
      (∀ j, 1 ≤ j → j ≤ n → star (ruiXuX P n j false) = ruiXuX P n j false) := by sorry

end Presentation

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
