-- Prove2me | Theorems.Thm_PI_WwEvalWork_eval_applyAt0
-- name    : PI.WwEvalWork.eval_applyAt0
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:32.671976+00:00
-- url     : https://prove2.me/theorems/efabe2fb-61fa-4d57-adb3-440355110fe2
-- title:
--   Ww Eval Work: eval apply At0
-- statement:
--   The Ww Eval Work construction uses the eval apply At0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionEvaluation/LsumEqOfSubset.lean#L80-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionEvaluation/LsumEqOfSubset.lean#L80-L87

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwEval
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionEvaluation_LsumEqOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WwEvalWork
open MvPolynomial
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {l : ℕ} [Fact l.Prime] {N0 N1 : ℕ}

theorem PI.WwEvalWork.eval_applyAt0 (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (x : Lt × ℕ × Fin N0 → ℂ_[l]) (P : MvPolynomial (PI.WwEval.KM.XZ Lt N0 N1) ℤ) :
    eval x (PI.WwEval.KM.applyAt0 N0 N1 l Th P) = Lsum (wt Th) (peval x P) := by sorry
