-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_funField_le_locRing_05b42bbb4ae4
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_funField_le_locRing_05b42bbb4ae4
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:43:51.902626+00:00
-- url     : https://prove2.me/theorems/06ddda60-2b09-4745-acaa-b84c7856a1d5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Function Field Number fun Field le loc Ring 05b42bbb4ae4: P2 M Ground Theory Heights  Heights Inter Regularity Function Field Number fun Field le l
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Function Field Number fun Field le loc Ring 05b42bbb4ae4 construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Function Field Number fun Field le loc Ring 05b42bbb4ae4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FunFieldLeLocRing.lean#L138-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FunFieldLeLocRing.lean#L138-L142

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FunFieldLeLocRing
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_funField_le_locRing_05b42bbb4ae4 (P : Ideal (MRing ι)) [P.IsPrime] : funField P ≤ locRing P P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityFunctionFieldNumber».«funField_le_locRing» := P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_funField_le_locRing_05b42bbb4ae4
