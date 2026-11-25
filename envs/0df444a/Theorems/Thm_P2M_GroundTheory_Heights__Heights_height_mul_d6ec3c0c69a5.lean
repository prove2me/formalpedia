-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_mul_d6ec3c0c69a5
-- name    : P2M_GroundTheory_Heights__Heights_height_mul_d6ec3c0c69a5
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:52.870253+00:00
-- url     : https://prove2.me/theorems/0ad12182-2e1d-46c3-88f1-ac3eac26e767
-- title:
--   P2 M Ground Theory Heights  Heights height mul d6ec3c0c69a5: P2 M Ground Theory Heights  Heights height mul d6ec3c0c69a5
-- statement:
--   The P2 M Ground Theory Heights  Heights height mul d6ec3c0c69a5 construction uses the P2 M Ground Theory Heights  Heights height mul d6ec3c0c69a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/Height.lean#L29-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/Height.lean#L29-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
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
open ReciprocityTheory.ChartRestriction.G NumberField
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_height_mul_d6ec3c0c69a5 (A B : HermLine n) {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    height (A.mul B) x = height A x + height B x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«height_mul» := P2M_GroundTheory_Heights__Heights_height_mul_d6ec3c0c69a5
