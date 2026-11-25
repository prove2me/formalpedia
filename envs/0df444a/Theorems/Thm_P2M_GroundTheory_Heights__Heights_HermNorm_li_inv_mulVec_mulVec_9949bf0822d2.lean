-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_inv_mulVec_mulVec_9949bf0822d2
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_li_inv_mulVec_mulVec_9949bf0822d2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:01.399746+00:00
-- url     : https://prove2.me/theorems/73ef1b2e-a5b7-4c86-a712-f868001591c4
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm li inv mul Vec mul Vec 9949bf0822d2: P2 M Ground Theory Heights  Heights Herm Norm li inv mul Vec mul Vec 9949bf0822d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm li inv mul Vec mul Vec 9949bf0822d2 construction uses the P2 M Ground Theory Heights  Heights Herm Norm li inv mul Vec mul Vec 9949bf0822d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L40-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.HermNorm
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HermNorm_li_inv_mulVec_mulVec_9949bf0822d2 (h : HermNorm n) (v : Fin n → ℂ) : h.mat⁻¹ *ᵥ (h.mat *ᵥ v) = v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«li_inv_mulVec_mulVec» := P2M_GroundTheory_Heights__Heights_HermNorm_li_inv_mulVec_mulVec_9949bf0822d2
