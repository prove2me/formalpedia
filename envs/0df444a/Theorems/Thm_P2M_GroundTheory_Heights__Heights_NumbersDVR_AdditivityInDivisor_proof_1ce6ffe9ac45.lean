-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_proof_1ce6ffe9ac45
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_proof_1ce6ffe9ac45
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:32:37.849806+00:00
-- url     : https://prove2.me/theorems/6ef835fa-c796-46bd-94ad-a61b79018a19
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor proof 1ce6ffe9ac45: P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor proof 1ce6ffe9ac45
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor proof 1ce6ffe9ac45 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Additivity In Divisor proof 1ce6ffe9ac45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WithBotLtOfAddOneLe.lean#L68-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WithBotLtOfAddOneLe.lean#L68-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WithBotLtOfAddOneLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_proof_1ce6ffe9ac45 (hmul : DivCycleMul.Statement.{u}) (hfin : DivCycleFiniteSupport.Statement.{u})
    (hadd : IntNumAddFirst.Statement.{u}) (hsup : SupSpanMultiHomog.Statement.{u})
    (hmin : MinimalPrimeMultiHomog.Statement.{u}) (hspm : SpecialIdealMultiHomog.Statement.{u})
    (hcor : SpecialIdealCorresp.Statement.{u}) (hqd : SpecialQuotDim.Statement.{u})
    (hdrop : DimStrictDrop.Statement.{u}) : AdditivityInDivisor.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«AdditivityInDivisor».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_proof_1ce6ffe9ac45
