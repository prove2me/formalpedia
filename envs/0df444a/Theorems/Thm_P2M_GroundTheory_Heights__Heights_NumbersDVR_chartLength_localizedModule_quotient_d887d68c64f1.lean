-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_chartLength_localizedModule_quotient_d887d68c64f1
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_chartLength_localizedModule_quotient_d887d68c64f1
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:11:08.540705+00:00
-- url     : https://prove2.me/theorems/7385c6a1-6fc9-49ec-8032-fd6002176fc3
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR chart Length localized Module quotient d887d68c64f1: P2 M Ground Theory Heights  Heights Numbers DVR chart Length localized Module quotient d887d68c64f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR chart Length localized Module quotient d887d68c64f1 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR chart Length localized Module quotient d887d68c64f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalChartLength.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalChartLength.lean#L16-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontalMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalChartLength
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_chartLength_localizedModule_quotient_d887d68c64f1 {A : Type*} [CommRing A] (K W : Ideal A) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ K)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«chartLength_localizedModule_quotient» := P2M_GroundTheory_Heights__Heights_NumbersDVR_chartLength_localizedModule_quotient_d887d68c64f1
