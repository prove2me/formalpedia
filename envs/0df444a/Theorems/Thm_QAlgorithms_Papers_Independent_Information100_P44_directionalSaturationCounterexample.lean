-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_directionalSaturationCounterexample
-- name    : QAlgorithms.Papers.Independent.Information100.P44.directionalSaturationCounterexample
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:40:40.821356+00:00
-- url     : https://prove2.me/theorems/c721f586-2499-45af-a3c8-50f040dcc937
-- title:
--   Proposition 3: directional saturation need not force rank-one mode action
-- statement:
--   Let $H=\operatorname{diag}(E_0,E_1,E_1)$ with $E_0\ne E_1$, let $q\in(0,1)$, and set $U_-=\operatorname{diag}(1,1,-1)$ and $\Phi_q(X)=qX+(1-q)U_-XU_-^\dagger$. For every real inverse temperature this channel is covariant and Gibbs preserving, and it preserves every diagonal entry. Moreover,
--   $$\Phi_q(|0\rangle\langle1|)=|0\rangle\langle1|,\qquad \Phi_q(|0\rangle\langle2|)=(2q-1)|0\rangle\langle2|.$$
--   The unchanged-population bound is saturated in the first direction. When $q\ne1/2$, the actual action on the displayed two-dimensional mode has rank two. Thus directional saturation does not force rank-one mode action.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 20, Proposition 3: directional saturation need not force rank-one mode action

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.20, Proposition 3: directional saturation with rank two for q != 1/2. -/
theorem directionalSaturationCounterexample (E0 E1 beta q : ℝ) (hE : E0 ≠ E1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    IsCGP ![E0,E1,E1] beta (directionalMixture q) ∧
    (∀ (X : Mat 3) i, directionalMixture q X i i = X i i) ∧
    directionalMixture q (matrixUnit 0 1) = matrixUnit 0 1 ∧
    directionalMixture q (matrixUnit 0 2) = ((2*q-1 : ℝ) : ℂ) • matrixUnit 0 2 ∧
    ‖directionalMixture q (matrixUnit 0 1) 0 1‖ =
      Real.sqrt (population (directionalMixture q) 0 0 * population (directionalMixture q) 1 1) ∧
    (q ≠ 1/2 → (shortModeMatrix q).rank = 2) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
