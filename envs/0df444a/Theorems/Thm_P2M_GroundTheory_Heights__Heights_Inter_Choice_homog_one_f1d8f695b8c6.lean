-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_one_f1d8f695b8c6
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_one_f1d8f695b8c6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:02.546684+00:00
-- url     : https://prove2.me/theorems/008bbbe0-8701-4565-a20a-40b8ef4a6f1f
-- title:
--   P2 M Ground Theory Heights  Heights Inter Choice homog one f1d8f695b8c6: P2 M Ground Theory Heights  Heights Inter Choice homog one f1d8f695b8c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Choice homog one f1d8f695b8c6 construction uses the P2 M Ground Theory Heights  Heights Inter Choice homog one f1d8f695b8c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L22-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.Choice
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_one_f1d8f695b8c6 : IsMultiHomog (1 : MRingOver R ι) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Choice».«homog_one» := P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_one_f1d8f695b8c6
