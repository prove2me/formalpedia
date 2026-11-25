-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_groupNorm_c0f46ee8c4b1
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_groupNorm_c0f46ee8c4b1
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:15.243752+00:00
-- url     : https://prove2.me/theorems/dbf53adb-82e9-492a-bdf1-ee130a2c1e30
-- title:
--   P2 M Ground Theory Heights  Heights Log Int integrable On log group Norm c0f46ee8c4b1: P2 M Ground Theory Heights  Heights Log Int integrable On log group Norm c0f46ee8c4b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int integrable On log group Norm c0f46ee8c4b1 construction uses the P2 M Ground Theory Heights  Heights Log Int integrable On log group Norm c0f46ee8c4b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L151-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L151-L206

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
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_groupNorm_c0f46ee8c4b1 (h : HermNorm n) (r : ℝ) (i : Fin k) :
    IntegrableOn (fun u : Fin k × Fin n → ℂ => Real.log (h.norm fun j => u (i, j)))
      (polydisc _ r) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«integrableOn_log_groupNorm» := P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_groupNorm_c0f46ee8c4b1
