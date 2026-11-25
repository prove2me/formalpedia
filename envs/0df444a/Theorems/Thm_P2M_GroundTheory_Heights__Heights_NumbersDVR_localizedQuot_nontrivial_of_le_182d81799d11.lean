-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_nontrivial_of_le_182d81799d11
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_nontrivial_of_le_182d81799d11
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:12:18.550035+00:00
-- url     : https://prove2.me/theorems/9e1b8fc0-fcdd-4c8d-8b44-c787f8b0f116
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR localized Quot nontrivial of le 182d81799d11: P2 M Ground Theory Heights  Heights Numbers DVR localized Quot nontrivial of le 182d81799d11
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR localized Quot nontrivial of le 182d81799d11 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR localized Quot nontrivial of le 182d81799d11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WithBotLtNatCastOfAddOneLe.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WithBotLtNatCastOfAddOneLe.lean#L20-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleFiniteSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WithBotLtNatCastOfAddOneLe
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
variable {A : Type*} [CommRing A]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_nontrivial_of_le_182d81799d11 (J W : Ideal A) [W.IsPrime] (h : J ≤ W) :
    Nontrivial (LocalizedModule W.primeCompl (A ⧸ J)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«localizedQuot_nontrivial_of_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_nontrivial_of_le_182d81799d11
