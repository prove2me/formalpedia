-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_mem_pointIdeal_join_iff_22ed8647669f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_mem_pointIdeal_join_iff_22ed8647669f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:07:39.276189+00:00
-- url     : https://prove2.me/theorems/fb98d64b-d345-4bf0-a646-ff8ab1152af5
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Point Model mem point Ideal join iff 22ed8647669f: P2 M Ground Theory Heights  Heights Numbers DVR Join Point Model mem point Ideal join iff 22ed86
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Point Model mem point Ideal join iff 22ed8647669f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Point Model mem point Ideal join iff 22ed8647669f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointModel.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointModel.lean#L73-L79

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_mem_pointIdeal_join_iff_22ed8647669f (y : (Σ k, ι k) → Ω)
    (p : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O) :
    p ∈ pointIdeal O (joinCoord y (ptCoord (Ω := Ω))) ↔
      srcEquiv O p ∈ RingHom.ker
        (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinPointModel».«mem_pointIdeal_join_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_mem_pointIdeal_join_iff_22ed8647669f
