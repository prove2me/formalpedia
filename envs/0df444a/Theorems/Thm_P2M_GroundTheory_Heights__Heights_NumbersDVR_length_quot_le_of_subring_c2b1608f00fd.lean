-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_quot_le_of_subring_c2b1608f00fd
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_length_quot_le_of_subring_c2b1608f00fd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:12:13.580429+00:00
-- url     : https://prove2.me/theorems/103443ba-2465-4e95-a801-e27f5e69c142
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR length quot le of subring c2b1608f00fd: P2 M Ground Theory Heights  Heights Numbers DVR length quot le of subring c2b1608f00fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR length quot le of subring c2b1608f00fd construction uses the P2 M Ground Theory Heights  Heights Numbers DVR length quot le of subring c2b1608f00fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpOrderLe.lean#L29-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpOrderLe.lean#L29-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpOrderLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_length_quot_le_of_subring_c2b1608f00fd (h₂ : LengthMapIdealLe.Statement.{u})
    (h₃ : IntermediateRingQuotLength.Statement.{u}) {A D : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing D] [IsDomain D] [IsLocalRing D] (hdim : ringKrullDim A = 1)
    (C : Subring D) (f : A →+* C) (hfinj : Function.Injective f)
    (hfrac : ∀ c : C, ∃ a, a ≠ 0 ∧ f a * c ∈ Set.range f)
    (hmax : IsLocalRing.maximalIdeal D ≤
      ((IsLocalRing.maximalIdeal D).comap C.subtype).map C.subtype)
    (a : A) (ha : a ≠ 0) :
    Module.length D (D ⧸ Ideal.span {(f a : D)}) ≤ Module.length A (A ⧸ Ideal.span {a}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«length_quot_le_of_subring» := P2M_GroundTheory_Heights__Heights_NumbersDVR_length_quot_le_of_subring_c2b1608f00fd
