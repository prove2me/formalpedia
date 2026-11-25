-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_ringKrullDim_join_ae569ee243f0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_ringKrullDim_join_ae569ee243f0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:08:01.243804+00:00
-- url     : https://prove2.me/theorems/0ae3fdd0-f498-4d98-86d4-23058ece15e4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Point Model ring Krull Dim join ae569ee243f0: P2 M Ground Theory Heights  Heights Numbers DVR Join Point Model ring Krull Dim join ae569ee243f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Point Model ring Krull Dim join ae569ee243f0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Point Model ring Krull Dim join ae569ee243f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointModel.lean#L81-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointModel.lean#L81-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointModel
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord joinCoord mcMap)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointModel
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_ringKrullDim_join_ae569ee243f0 [IsNoetherianRing O] (y : (Σ k, ι k) → Ω) :
    ringKrullDim (MRing (Sum.elim ι ptIdx) O ⧸ pointIdeal O (joinCoord y (ptCoord (Ω := Ω)))) =
      ringKrullDim (MRing ι O ⧸ pointIdeal O y) + 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinPointModel».«ringKrullDim_join» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_ringKrullDim_join_ae569ee243f0
