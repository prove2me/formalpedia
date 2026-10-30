-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_tensorPhaseMaximum
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.tensorPhaseMaximum
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:53:13.069044+00:00
-- url     : https://prove2.me/theorems/0c25574f-75fa-4c60-acc9-f48c0fd7dcff
-- title:
--   Remark IV.1(2): phase absorption
-- statement:
--   Let $r>0$ and $N_k>0$, and let $X$ be any complex tensor with the conjugate-linear-first inner product (176). Over unit vectors $z_k\in\mathbb C^{N_k}$, both maxima below are attained and
--   $$\max_{\|z_k\|_2=1}|\langle X,\bigotimes_a z_k\rangle|=\max_{\|z_k\|_2=1}\operatorname{Re}\langle X,\bigotimes_a z_k\rangle.$$
--   Every tuple maximizing the real part also maximizes the absolute value. No converse for the same phased tuple is claimed. Positive tensor order permits absorption of a phase into one factor.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 29, Remark IV.1(2): phase absorption

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Remark IV.1(2), PDF p.29: equal attained maxima and the implication
for real-part maximizers, without the false converse for fixed phases. -/
theorem tensorPhaseMaximum {r : ℕ} (hr : 0 < r) (d : Fin r → ℕ)
    (hd : ∀ k, 0 < d k) (X : ArrayIndex d → ℂ) :
    (∃ v : ℝ,
      IsGreatest {v | ∃ z : (k : Fin r) → Fin (d k) → ℂ,
        unitTensorFactors z ∧ v = ‖vInner X (tensorProduct z)‖} v ∧
      IsGreatest {v | ∃ z : (k : Fin r) → Fin (d k) → ℂ,
        unitTensorFactors z ∧ v = (vInner X (tensorProduct z)).re} v) ∧
    ∀ z : (k : Fin r) → Fin (d k) → ℂ, unitTensorFactors z →
      (∀ w : (k : Fin r) → Fin (d k) → ℂ, unitTensorFactors w →
        (vInner X (tensorProduct w)).re ≤ (vInner X (tensorProduct z)).re) →
      ∀ w : (k : Fin r) → Fin (d k) → ℂ, unitTensorFactors w →
        ‖vInner X (tensorProduct w)‖ ≤ ‖vInner X (tensorProduct z)‖ := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
