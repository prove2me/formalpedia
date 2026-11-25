-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_smul_549dac818b96
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_smul_549dac818b96
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:33.695099+00:00
-- url     : https://prove2.me/theorems/8bf36fca-3363-5b19-88e1-ea01da06997a
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm li norm smul 549dac818b96: P2 M Ground Theory Heights  Heights Herm Norm li norm smul 549dac818b96
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm li norm smul 549dac818b96 construction uses the P2 M Ground Theory Heights  Heights Herm Norm li norm smul 549dac818b96 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L22-L31

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

theorem P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_smul_549dac818b96 (h : HermNorm n) (a : ℂ) (v : Fin n → ℂ) :
    h.norm (fun j => a * v j) = ‖a‖ * h.norm v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«li_norm_smul» := P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_smul_549dac818b96
