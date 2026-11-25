-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_cycEval_add_cycle_ad3e7e5b4611
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_cycEval_add_cycle_ad3e7e5b4611
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:40.165107+00:00
-- url     : https://prove2.me/theorems/9f57ac9f-a557-4758-80cd-b74fce14ace8
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor cyc Eval add cycle ad3e7e5b4611: P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor cyc Eval add cycle ad3e7e5b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor cyc Eval add cycle ad3e7e5b4611 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor cyc Eval add cycle ad3e7e5b4611 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WithBotLtOfAddOneLe.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WithBotLtOfAddOneLe.lean#L15-L20

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_cycEval_add_cycle_ad3e7e5b4611 {n Z₁ Z₂ : Ideal (MRing ι R) → ℤ} (h₁ : (Function.support Z₁).Finite)
    (h₂ : (Function.support Z₂).Finite) : cycEval n (Z₁ + Z₂) = cycEval n Z₁ + cycEval n Z₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«AdditivityInDivisor».«cycEval_add_cycle» := P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_cycEval_add_cycle_ad3e7e5b4611
