-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_aeval_ratioVec_surjective_f11ca01af460
-- name    : P2M_GroundTheory_Heights__Heights_aeval_ratioVec_surjective_f11ca01af460
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:04.326832+00:00
-- url     : https://prove2.me/theorems/a6e71a6b-0f64-4ceb-94d3-ee6d314c99f7
-- title:
--   P2 M Ground Theory Heights  Heights aeval ratio Vec surjective f11ca01af460: P2 M Ground Theory Heights  Heights aeval ratio Vec surjective f11ca01af460
-- statement:
--   The P2 M Ground Theory Heights  Heights aeval ratio Vec surjective f11ca01af460 construction uses the P2 M Ground Theory Heights  Heights aeval ratio Vec surjective f11ca01af460 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatio.lean#L23-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatio.lean#L23-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatioLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_aeval_ratioVec_surjective_f11ca01af460 (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) :
    Function.Surjective (aeval (ratioVec x c) : MvPolynomial (Coord n) ℚ →ₐ[ℚ] ratioField x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«aeval_ratioVec_surjective» := P2M_GroundTheory_Heights__Heights_aeval_ratioVec_surjective_f11ca01af460
