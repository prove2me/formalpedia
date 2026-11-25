-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projLineFlag_pushforward_hypotheses_adf4562d72f1
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projLineFlag_pushforward_hypotheses_adf4562d72f1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:32:35.995231+00:00
-- url     : https://prove2.me/theorems/7cd15388-8e52-5b05-8dae-1b6dd0e2d990
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Line Flag pushforward hypotheses adf4562d72f1: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pr
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Line Flag pushforward hypotheses adf4562d72f1 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Line Flag pushforward hypotheses adf4562d72f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ProjLineRankTwoPushforwardHypotheses.lean#L309-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ProjLineRankTwoPushforwardHypotheses.lean#L309-L318

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projLineFlag_pushforward_hypotheses_adf4562d72f1 :
    flagDim 3 = 3 ∧
    IsArithVar (⊥ : Ideal (MRing (GlobalTheory 2))) 2 ∧ IsQuotRows (⊥ : Ideal (MRing (GlobalTheory 2))) (noRows 3) 0 3 ∧
    IsKerBasis (⊥ : Ideal (MRing (GlobalTheory 2))) (noRows 3) (idRows 3) ∧ AllSmooth ![fsO1 2, fsO1 2] ∧
    (∀ j, IsPullHerm Sum.inl (inlV (ι := GlobalTheory 2) (ι₂ := PluckerBlocks 3 3)) (![fsO1 2, fsO1 2] j)
      (pullHerm isBlockMap_inl (![fsO1 2, fsO1 2] j))) ∧
    AllSmooth (fun _ : Fin (flagDim 3) => pluckerFubiniStudyO1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«projLineFlag_pushforward_hypotheses» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projLineFlag_pushforward_hypotheses_adf4562d72f1
