-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pfAI3_hyps_b91d1ed5823d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pfAI3_hyps_b91d1ed5823d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:26:00.387818+00:00
-- url     : https://prove2.me/theorems/8e5316e1-b4b6-47a5-88ee-1b07e5d8374e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pf AI3 hyps b91d1ed5823d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pf AI3 hyps b91d1ed5823d
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pf AI3 hyps b91d1ed5823d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pf AI3 hyps b91d1ed5823d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ProjLineRankTwoPushforwardHypotheses.lean#L271-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ProjLineRankTwoPushforwardHypotheses.lean#L271-L277

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I4_isBlockMap_id

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pfAI3_hyps_b91d1ed5823d :
    IsBlockMap (ι := GlobalTheory 2) (ι' := GlobalTheory 2) id id ∧ IsArithVar (⊥ : Ideal (MRing (GlobalTheory 2))) 2 ∧
    imageZ (ι := GlobalTheory 2) (ι' := GlobalTheory 2) id ⊥ = ⊥ ∧ IsChart (fibreIdeal id genFibreId) chartId ∧
    AllSmooth ![fsO1 2, fsO1 2] ∧
    ∀ j, IsPullHerm id id (![fsO1 2, fsO1 2] j) (pullHerm isBlockMap_id (![fsO1 2, fsO1 2] j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«pfAI3_hyps» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pfAI3_hyps_b91d1ed5823d
