-- Prove2me | Theorems.Thm_PI_WGB_minorA_RInv
-- name    : PI.WGB.minorA_RInv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:46:09.211663+00:00
-- url     : https://prove2.me/theorems/988f6709-b5fc-558f-a668-59fd080d809f
-- title:
--   WGB: minor A RInv
-- statement:
--   The WGB construction uses the minor A RInv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/StepACleared.lean#L127-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/StepACleared.lean#L127-L129

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

theorem PI.WGB.minorA_RInv (s : ℕ) (hr : s ≤ n + 1) :
    RInvA (fun x : Fin (n + 1) × Fin (n + 1) → ℂ => eval x (lpMinor ℂ s hr hr)) := by sorry
