-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_abs_log_eval_monomial_le_93b90b5d28e6
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_abs_log_eval_monomial_le_93b90b5d28e6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:43.964039+00:00
-- url     : https://prove2.me/theorems/f9c6c058-1a11-4214-ad7a-8b0107fffa39
-- title:
--   P2 M Ground Theory Heights  Heights Log Int abs log eval monomial le 93b90b5d28e6: P2 M Ground Theory Heights  Heights Log Int abs log eval monomial le 93b90b5d28e6
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int abs log eval monomial le 93b90b5d28e6 construction uses the P2 M Ground Theory Heights  Heights Log Int abs log eval monomial le 93b90b5d28e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L140-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L140-L161

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_abs_log_eval_monomial_le_93b90b5d28e6 (m : ι →₀ ℕ) (c : ℂ) (u : ι → ℂ) :
    |Real.log ‖eval u (monomial m c)‖| ≤
      |Real.log ‖c‖| + ∑ i ∈ m.support, (m i : ℝ) * |Real.log ‖u i‖| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«abs_log_eval_monomial_le» := P2M_GroundTheory_Heights__Heights_LogInt_abs_log_eval_monomial_le_93b90b5d28e6
