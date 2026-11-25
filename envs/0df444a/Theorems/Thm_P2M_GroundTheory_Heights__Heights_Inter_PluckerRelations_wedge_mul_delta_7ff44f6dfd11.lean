-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_wedge_mul_delta_7ff44f6dfd11
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_wedge_mul_delta_7ff44f6dfd11
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:42:02.283051+00:00
-- url     : https://prove2.me/theorems/71c33c55-0600-4296-84a5-b35c371450bc
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Relations wedge mul delta 7ff44f6dfd11: P2 M Ground Theory Heights  Heights Inter Plucker Relations wedge mul delta 7ff44f6dfd11
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Relations wedge mul delta 7ff44f6dfd11 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Relations wedge mul delta 7ff44f6dfd11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean#L59-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean#L59-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerRel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerRel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerRelations
variable {D : ℕ} (S : ProjectiveLineBundle D)

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_wedge_mul_delta_7ff44f6dfd11 (i : S.ι) (hi : S.x i ≠ 0) (l : S.ν) (k m : S.κ) :
    ∃ a ∈ chartRing ℤ S.x i, wedgeVal S k m * S.δ l = S.x i ^ 3 * a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerRelations».«wedge_mul_delta» := P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_wedge_mul_delta_7ff44f6dfd11
