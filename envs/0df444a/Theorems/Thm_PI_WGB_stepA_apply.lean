-- Prove2me | Theorems.Thm_PI_WGB_stepA_apply
-- name    : PI.WGB.stepA_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:45:05.268468+00:00
-- url     : https://prove2.me/theorems/ba10634f-5a93-475b-a770-1a0e077e9a4b
-- title:
--   WGB: step A apply
-- statement:
--   The WGB construction uses the step A apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/StepACleared.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/StepACleared.lean#L63-L70

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}

theorem PI.WGB.stepA_apply (p q : Fin (n + 1)) (x : Fin (n + 1) × Fin (n + 1) → ℂ) (a j : Fin (n + 1)) :
    stepA p q x (a, j) =
      (if p < a ∧ a.val < n then x (a, j) + -(x (a, q) / x (p, q)) * x (p, j) else x (a, j)) +
      (if q < j then -(x (p, j) / x (p, q)) *
        (if p < a ∧ a.val < n then x (a, q) + -(x (a, q) / x (p, q)) * x (p, q) else x (a, q)) else 0) := by sorry
