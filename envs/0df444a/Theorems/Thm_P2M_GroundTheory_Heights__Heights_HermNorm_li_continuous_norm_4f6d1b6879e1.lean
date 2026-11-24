-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_continuous_norm_4f6d1b6879e1
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_li_continuous_norm_4f6d1b6879e1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:44.949856+00:00
-- url     : https://prove2.me/theorems/139265a0-54e1-4ff8-8d0d-25eeedc7cc21
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm li continuous norm 4f6d1b6879e1: P2 M Ground Theory Heights  Heights Herm Norm li continuous norm 4f6d1b6879e1
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm li continuous norm 4f6d1b6879e1 construction uses the P2 M Ground Theory Heights  Heights Herm Norm li continuous norm 4f6d1b6879e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L18-L20

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

theorem P2M_GroundTheory_Heights__Heights_HermNorm_li_continuous_norm_4f6d1b6879e1 (h : HermNorm n) : Continuous h.norm := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«li_continuous_norm» := P2M_GroundTheory_Heights__Heights_HermNorm_li_continuous_norm_4f6d1b6879e1
