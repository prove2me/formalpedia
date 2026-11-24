-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_int_relation_bf34191512a6
-- name    : P2M_GroundTheory_Heights__Heights_exists_int_relation_bf34191512a6
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:44.514881+00:00
-- url     : https://prove2.me/theorems/edcf43f4-6fd1-49d2-9993-429bd2107b87
-- title:
--   P2 M Ground Theory Heights  Heights exists int relation bf34191512a6: P2 M Ground Theory Heights  Heights exists int relation bf34191512a6
-- statement:
--   The P2 M Ground Theory Heights  Heights exists int relation bf34191512a6 construction uses the P2 M Ground Theory Heights  Heights exists int relation bf34191512a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegree.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegree.lean#L71-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
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

theorem P2M_GroundTheory_Heights__Heights_exists_int_relation_bf34191512a6 (r : AlgebraicClosure ℚ) :
    ∃ g : Polynomial ℤ, g ≠ 0 ∧ Polynomial.aeval r g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_int_relation» := P2M_GroundTheory_Heights__Heights_exists_int_relation_bf34191512a6
