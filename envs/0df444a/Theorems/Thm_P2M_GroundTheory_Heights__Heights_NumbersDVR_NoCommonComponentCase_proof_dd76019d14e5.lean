-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NoCommonComponentCase_proof_dd76019d14e5
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_NoCommonComponentCase_proof_dd76019d14e5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:34:00.103083+00:00
-- url     : https://prove2.me/theorems/668abf2d-3bd1-48e2-94bf-68aa3699c962
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR No Common Component Case proof dd76019d14e5: P2 M Ground Theory Heights  Heights Numbers DVR No Common Component Case proof dd76019d14e5
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR No Common Component Case proof dd76019d14e5 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR No Common Component Case proof dd76019d14e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ImportsMore.lean#L13-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ImportsMore.lean#L13-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMore
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialIdealCorresp_proof_bd738eb41ba7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialIdealMultiHomog_proof_41306882bd1b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialQuotDim_proof_5536281ab8d6

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_NoCommonComponentCase_proof_dd76019d14e5 (h₁ : LeftExpansion.Statement.{u}) (h₂ : RightExpansion.Statement.{u})
    (h₃ : LocalCoefficient.Statement.{u}) (h₄ : IntNumVanish.Statement.{u}) :
    NoCommonComponentCase.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«NoCommonComponentCase».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_NoCommonComponentCase_proof_dd76019d14e5
