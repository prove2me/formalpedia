-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_eta_negConj_2fb1bbadea8b
-- name    : P2M_GroundTheory_Heights__Theta_eta_negConj_2fb1bbadea8b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:53:19.065084+00:00
-- url     : https://prove2.me/theorems/8f60f77d-ec9c-586e-869d-50981ddce56e
-- title:
--   P2 M Ground Theory Heights  Theta eta neg Conj 2fb1bbadea8b: P2 M Ground Theory Heights  Theta eta neg Conj 2fb1bbadea8b
-- statement:
--   The P2 M Ground Theory Heights  Theta eta neg Conj 2fb1bbadea8b construction uses the P2 M Ground Theory Heights  Theta eta neg Conj 2fb1bbadea8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmEtaLogPeriodNegConjPf.lean#L21-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmEtaLogPeriodNegConjPf.lean#L21-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularForm Complex
open scoped Real

theorem P2M_GroundTheory_Heights__Theta_eta_negConj_2fb1bbadea8b (τ : ℍ) : η (negConj τ : ℂ) = starRingEnd ℂ (η (τ : ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«eta_negConj» := P2M_GroundTheory_Heights__Theta_eta_negConj_2fb1bbadea8b
