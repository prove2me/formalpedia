-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_eq_zero_of_norm_eq_zero_6c76e467f5e9
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_li_eq_zero_of_norm_eq_zero_6c76e467f5e9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:59.105358+00:00
-- url     : https://prove2.me/theorems/e762c736-bbd8-4104-8f83-848eee2af360
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm li eq zero of norm eq zero 6c76e467f5e9: P2 M Ground Theory Heights  Heights Herm Norm li eq zero of norm eq zero 6c76e467f5e9
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm li eq zero of norm eq zero 6c76e467f5e9 construction uses the P2 M Ground Theory Heights  Heights Herm Norm li eq zero of norm eq zero 6c76e467f5e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L59-L64

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

theorem P2M_GroundTheory_Heights__Heights_HermNorm_li_eq_zero_of_norm_eq_zero_6c76e467f5e9 (h : HermNorm n) (v : Fin n → ℂ) (hv : h.norm v = 0) : v = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«li_eq_zero_of_norm_eq_zero» := P2M_GroundTheory_Heights__Heights_HermNorm_li_eq_zero_of_norm_eq_zero_6c76e467f5e9
