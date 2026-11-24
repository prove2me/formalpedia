-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_eval_6d9e8a0784fc
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_eval_6d9e8a0784fc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:28.296593+00:00
-- url     : https://prove2.me/theorems/b9550253-f609-4e25-847a-16b4f1a7d042
-- title:
--   P2 M Ground Theory Heights  Heights Log Int integrable On log norm eval 6d9e8a0784fc: P2 M Ground Theory Heights  Heights Log Int integrable On log norm eval 6d9e8a0784fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int integrable On log norm eval 6d9e8a0784fc construction uses the P2 M Ground Theory Heights  Heights Log Int integrable On log norm eval 6d9e8a0784fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L277-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L277-L280

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
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
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_eval_6d9e8a0784fc [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) (r : ℝ) :
    IntegrableOn (fun u => Real.log ‖eval u g‖) (polydisc ι r) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«integrableOn_log_norm_eval» := P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_eval_6d9e8a0784fc
