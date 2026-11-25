-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_withBot_lt_of_add_one_le_ca3eb079d909
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_withBot_lt_of_add_one_le_ca3eb079d909
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:19.646807+00:00
-- url     : https://prove2.me/theorems/6bc6d149-8963-4316-95c7-5f1dec1c046b
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor with Bot lt of add one le ca3eb079d909: P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor with Bot lt of add o
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor with Bot lt of add one le ca3eb079d909 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor with Bot lt of add one le ca3eb079d909 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WithBotLtOfAddOneLe.lean#L40-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WithBotLtOfAddOneLe.lean#L40-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WithBotLtOfAddOneLe
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
open GroundTheory.Heights₂.Heights.NumbersDVR.AdditivityInDivisor
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_withBot_lt_of_add_one_le_ca3eb079d909 {x : WithBot ℕ∞} {n : ℕ} (hx : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«AdditivityInDivisor».«withBot_lt_of_add_one_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_withBot_lt_of_add_one_le_ca3eb079d909
