-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_ratDiv_support_finite_137b8be27f7f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_ratDiv_support_finite_137b8be27f7f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:11:46.350803+00:00
-- url     : https://prove2.me/theorems/60d79fa1-a2ce-564a-9cef-c18b42089657
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor rat Div support finite 137b8be27f7f: P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor rat Div support finite
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor rat Div support finite 137b8be27f7f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor rat Div support finite 137b8be27f7f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WithBotLtOfAddOneLe.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WithBotLtOfAddOneLe.lean#L32-L38

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_ratDiv_support_finite_137b8be27f7f {P : Ideal (MRing ι R)} {f g : MRing ι R}
    (hf : (Function.support (divCycle P f)).Finite) (hg : (Function.support (divCycle P g)).Finite) :
    (Function.support (ratDiv P f g)).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«AdditivityInDivisor».«ratDiv_support_finite» := P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_ratDiv_support_finite_137b8be27f7f
