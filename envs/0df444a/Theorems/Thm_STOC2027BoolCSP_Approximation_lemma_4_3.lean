-- Prove2me | Theorems.Thm_STOC2027BoolCSP_Approximation_lemma_4_3
-- name    : STOC2027BoolCSP.Approximation.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:55.692039+00:00
-- url     : https://prove2.me/theorems/da8dfdb6-5926-4718-a38a-e4213114939d
-- title:
--   Lemma 4.3 — precision in the common direction
-- statement:
--   Let $R$ be a real symmetric positive definite $m\times m$ matrix and $\eta>0$ with $R\succeq\eta J$, $J$ the all-ones matrix. Then
--   $$\mathbf 1^{\mathsf T}R^{-1}\mathbf 1\;\le\;\eta^{-1}.$$
--
--   No unit diagonal is assumed. The lemma converts the common covariance component of a clause into a bound on the quadratic term of the potential (9) at a uniform test point.
--
--   Differences from the source: none.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 8 (PDF 11), Lemma 4.3

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Gaussian

open Matrix

namespace STOC2027BoolCSP.Approximation

/-- Lemma 4.3 (precision in the common direction), printed p. 8: if `R ≻ 0` and `R ⪰ ηJ` with
`η > 0`, then `1ᵀR⁻¹1 ≤ η⁻¹`. No unit diagonal is assumed. -/
theorem lemma_4_3 (m : ℕ) (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef) (η : ℝ) (hη : 0 < η)
    (hRJ : (R - η • onesMat m).PosSemidef) :
    (fun _ => (1 : ℝ)) ⬝ᵥ (R⁻¹ *ᵥ fun _ => (1 : ℝ)) ≤ η⁻¹ := by sorry

end STOC2027BoolCSP.Approximation
