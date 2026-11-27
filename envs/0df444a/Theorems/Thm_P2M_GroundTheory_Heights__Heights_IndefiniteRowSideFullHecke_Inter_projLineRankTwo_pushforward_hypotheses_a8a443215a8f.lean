-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projLineRankTwo_pushforward_hypotheses_a8a443215a8f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projLineRankTwo_pushforward_hypotheses_a8a443215a8f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:26:04.493343+00:00
-- url     : https://prove2.me/theorems/b9f82ed4-b4bd-4aad-8229-6e5b5d5347e4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Line Rank Two pushforward hypotheses a8a443215a8f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inte
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Line Rank Two pushforward hypotheses a8a443215a8f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Line Rank Two pushforward hypotheses a8a443215a8f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ProjLineRankTwoPushforwardHypotheses.lean#L297-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ProjLineRankTwoPushforwardHypotheses.lean#L297-L305

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I4_isBlockMap_inl

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projLineRankTwo_pushforward_hypotheses_a8a443215a8f :
    IsArithVar (⊥ : Ideal (MRing (GlobalTheory 2))) 2 ∧ IsQuotRows (⊥ : Ideal (MRing (GlobalTheory 2))) (noRows 2) 0 2 ∧
    IsKerBasis (⊥ : Ideal (MRing (GlobalTheory 2))) (noRows 2) (idRows 2) ∧ AllSmooth ![fsO1 2, fsO1 2] ∧
    (∀ j, IsPullHerm Sum.inl (inlV (ι := GlobalTheory 2) (ι₂ := fun _ : Unit => Fin 2)) (![fsO1 2, fsO1 2] j)
      (pullHerm isBlockMap_inl (![fsO1 2, fsO1 2] j))) ∧
    IsSmoothHerm fibreFubiniStudyO1 ∧ fibreFubiniStudyO1.a (Sum.inr ()) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«projLineRankTwo_pushforward_hypotheses» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projLineRankTwo_pushforward_hypotheses_a8a443215a8f
