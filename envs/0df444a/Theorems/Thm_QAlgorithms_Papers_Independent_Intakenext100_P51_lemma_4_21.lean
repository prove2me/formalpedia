-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_lemma_4_21
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.lemma_4_21
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:02:03.650151+00:00
-- url     : https://prove2.me/theorems/0fc15b86-faf4-41b4-b823-7090aa44c26c
-- title:
--   Constructed central Laurent moments and complete series recurrence
-- statement:
--   Let $r\ge1$ and let $R$ be a commutative unital ring. Fix units $q,\delta,\rho,u_1,\ldots,u_r$, with $\delta=q-q^{-1}$, and moments $\omega_a\in R$ for $a\in\mathbb Z$, with $\omega_0=1-\delta^{-1}(\rho-\rho^{-1})$. Let $B_{r,n}$ be the algebra of Definition 2.1 with all its specified relations. No nonzero or invertibility assumption on $\omega_0$ is made. Assume that the parameters are $\mathbf u$-admissible in the sense of Definition 3.15.
--
--   Put $t=y^{-1}$ and $D=\delta^{-1}\rho$. Starting with $\widetilde W_1(y)=\sum_{a\ge0}\omega_a y^{-a}$, define $\widetilde W_k$ by the ordered product (4.28), expanded at infinity. Thus, with $F_k=\widetilde W_k+D-y^2/(y^2-1)$, multiply $F_1$ by the factors
--   $$
--   R_i(y)=\frac{(y-X_i)^2}{(y-X_i^{-1})^2}\frac{y-q^{-2}X_i^{-1}}{y-q^{-2}X_i}\frac{y-q^2X_i^{-1}}{y-q^2X_i},\qquad 1\le i<k,
--   $$
--   using their complete geometric expansions. Write $\omega_k^{(a)}$ for the resulting coefficient of $y^{-a}$.
--
--   For every $k\ge1$, $a\ge0$, and ambient level $n\ge k+1$, the coefficient computed at level $k-1$ belongs to $Z(B_{r,k-1})\cap R[X_1^{\pm1},\ldots,X_{k-1}^{\pm1}]$, and its canonical ambient evaluation satisfies
--   $$
--   E_kX_k^aE_k=\omega_k^{(a)}E_k,\qquad
--   F_{k+1}(y)(y-X_k^{-1})^2(y-q^{-2}X_k)(y-q^2X_k)
--   =F_k(y)(y-X_k)^2(y-q^{-2}X_k^{-1})(y-q^2X_k^{-1}).
--   $$
--
--   This constructs the central moments and preserves the complete recurrence (4.22). The series identity is cross-multiplied; it does not require a fraction field for a noncommutative algebra. At level zero the coefficient algebra is the scalar algebra.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 17, Lemma 4.21

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section CentralSeries

variable {R : Type*} [CommRing R] {r : ℕ} (P : Ground R r)

/-- Lemma 4.21, PDF p.17: the explicitly computed coefficients lie in the
center AND Laurent subalgebra of the actual level k-1 algebra, satisfy the
sandwich identity at every ambient level n>=k+1, and obey the complete
cross-multiplied series recurrence (4.22). Only ring-level hypotheses apply. -/
theorem lemma_4_21 (hu : RuiXuUAdmissible P) (n k a : ℕ) (hk : 1 ≤ k ∧ k < n) :
    ruiXuCentralMoment P (k-1) k a ∈ laurentImage P (k-1) (k-1) ∧
    (∀ b : RuiXuBMW P (k-1), ruiXuCentralMoment P (k-1) k a * b = b * ruiXuCentralMoment P (k-1) k a) ∧
    ruiXuE P n k * ruiXuX P n k false ^ a * ruiXuE P n k = ruiXuCentralMoment P n k a * ruiXuE P n k ∧
    shiftedMomentProduct P n k * transitionDenominator P n k =
      shiftedMomentProduct P n (k-1) * transitionNumerator P n k := by sorry

end CentralSeries

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
