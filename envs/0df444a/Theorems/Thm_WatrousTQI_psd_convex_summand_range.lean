-- Prove2me | Theorems.Thm_WatrousTQI_psd_convex_summand_range
-- name    : WatrousTQI.psd_convex_summand_range
-- status  : Open
-- author  : @Mrnaiq
-- created : 2026-11-12T22:35:20.446212+00:00
-- url     : https://prove2.me/theorems/5ce2c39c-0dfd-45cf-a407-d056e247d4f1
-- title:
--   Theorem 2.31 proof — support of positive convex summands
-- statement:
--   Let $Q_0,Q_1$ be positive semidefinite complex $n\times n$ matrices, $n>0$, and let $0<t<1$. If $$P=tQ_0+(1-t)Q_1,$$ then $$\operatorname{im}Q_0\subseteq\operatorname{im}P,\qquad\operatorname{im}Q_1\subseteq\operatorname{im}P.$$ Both coefficients are strictly positive; no invertibility or fixed rank is assumed. This isolates the support-containment step used for Choi matrices of channels in a proper convex decomposition.
-- source:
--   John Watrous, The Theory of Quantum Information, Cambridge University Press, 2018, Section 2.2.4, printed pp.96–99. https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf; Proof of Theorem 2.31, equations (2.179)–(2.181), printed p.97; the second inclusion follows by exchanging the two summands.

import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder BigOperators

namespace WatrousTQI
theorem psd_convex_summand_range {n : ℕ} (hn : 0 < n)
    (P Q₀ Q₁ : Matrix (Fin n) (Fin n) ℂ)
    (h₀ : Q₀.PosSemidef) (h₁ : Q₁.PosSemidef)
    (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1)
    (hP : P = t • Q₀ + (1 - t) • Q₁) :
    LinearMap.range Q₀.mulVecLin ≤ LinearMap.range P.mulVecLin ∧
    LinearMap.range Q₁.mulVecLin ≤ LinearMap.range P.mulVecLin := by sorry
end WatrousTQI
