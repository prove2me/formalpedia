-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_tgtEquiv_mcMap_818d2f828477
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_tgtEquiv_mcMap_818d2f828477
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:08:57.984911+00:00
-- url     : https://prove2.me/theorems/90440197-b888-4a02-9414-f122358cfe09
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Point Model tgt Equiv mc Map 818d2f828477: P2 M Ground Theory Heights  Heights Numbers DVR Join Point Model tgt Equiv mc Map 818d2f828477
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Point Model tgt Equiv mc Map 818d2f828477 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Point Model tgt Equiv mc Map 818d2f828477 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointModel.lean#L58-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointModel.lean#L58-L71

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_tgtEquiv_mcMap_818d2f828477 (y : (Σ k, ι k) → Ω) (p : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O) :
    tgtEquiv K Ω (mcMap O (joinCoord y (ptCoord (Ω := Ω))) p) =
      Polynomial.map (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω) (srcEquiv O p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinPointModel».«tgtEquiv_mcMap» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_tgtEquiv_mcMap_818d2f828477
