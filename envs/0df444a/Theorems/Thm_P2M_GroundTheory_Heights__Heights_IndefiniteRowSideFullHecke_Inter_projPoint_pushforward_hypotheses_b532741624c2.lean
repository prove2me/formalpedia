-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projPoint_pushforward_hypotheses_b532741624c2
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projPoint_pushforward_hypotheses_b532741624c2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:29.9458+00:00
-- url     : https://prove2.me/theorems/04aeeb2b-821d-452c-b391-1b45b580204f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Point pushforward hypotheses b532741624c2: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj P
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Point pushforward hypotheses b532741624c2 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Point pushforward hypotheses b532741624c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ProjLineRankTwoPushforwardHypotheses.lean#L213-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ProjLineRankTwoPushforwardHypotheses.lean#L213-L228

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I4_isBlockMap_blkV

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projPoint_pushforward_hypotheses_b532741624c2 :
    IsBlockMap (blkOf 0) (blkV (Fin 2) 0) ∧ IsArithVar (⊥ : Ideal (MRing ProjLineSquareBlocks)) 3 ∧
    IsArithVar (⊥ : Ideal (MRing (GlobalTheory 2))) 2 ∧
    (⊥ : Ideal (MRing (GlobalTheory 2))) ≤ imageZ (blkV (Fin 2) 0) (⊥ : Ideal (MRing ProjLineSquareBlocks)) ∧
    ringKrullDim (MRing (GlobalTheory 2) ⧸ imageZ (blkV (Fin 2) 0) (⊥ : Ideal (MRing ProjLineSquareBlocks))) <
      ((3 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ∧
    AllSmooth (fun _ : Fin 3 => fsO1 2) ∧
    ∀ _ : Fin 3, IsPullHerm (blkOf 0) (blkV (Fin 2) 0) (fsO1 2)
      (pullHerm (isBlockMap_blkV (Fin 2) 0) (fsO1 2)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«projPoint_pushforward_hypotheses» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projPoint_pushforward_hypotheses_b532741624c2
