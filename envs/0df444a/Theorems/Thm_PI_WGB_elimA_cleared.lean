-- Prove2me | Theorems.Thm_PI_WGB_elimA_cleared
-- name    : PI.WGB.elimA_cleared
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:44:25.675273+00:00
-- url     : https://prove2.me/theorems/5a467b22-147b-4e15-8f50-f6db8142cae9
-- title:
--   WGB: elim A cleared
-- statement:
--   The WGB construction uses the elim A cleared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/StepACleared.lean#L131-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/StepACleared.lean#L131-L151

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

theorem PI.WGB.elimA_cleared (x : Fin (n + 1) × Fin (n + 1) → ℂ)
    (hx : ∀ (s : ℕ) (hs : s + 1 ≤ n), eval x (lpMinor ℂ (s + 1) (by omega) (by omega) :
      MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ≠ 0) :
    ∀ k, k ≤ n → clearedA k (elimA k x) := by sorry
