-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_continuous_pointOf_0847939ca07e
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_continuous_pointOf_0847939ca07e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:12.491316+00:00
-- url     : https://prove2.me/theorems/ee46c1c4-5158-4526-a243-d74aae436a23
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm continuous point Of 0847939ca07e: P2 M Ground Theory Heights  Heights Herm Norm continuous point Of 0847939ca07e
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm continuous point Of 0847939ca07e construction uses the P2 M Ground Theory Heights  Heights Herm Norm continuous point Of 0847939ca07e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeIntegralLine.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeIntegralLine.lean#L13-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine
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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HermNorm_continuous_pointOf_0847939ca07e (h : HermNorm n) : Continuous h.pointOf := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«continuous_pointOf» := P2M_GroundTheory_Heights__Heights_HermNorm_continuous_pointOf_0847939ca07e
