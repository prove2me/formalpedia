-- Prove2me | Theorems.Thm_PI_WGB_stepA_cleared
-- name    : PI.WGB.stepA_cleared
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:44:55.151059+00:00
-- url     : https://prove2.me/theorems/e0ecfdc3-d8b8-41be-b276-3d2c2d74eaa2
-- title:
--   WGB: step A cleared
-- statement:
--   The WGB construction uses the step A cleared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/StepACleared.lean#L72-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/StepACleared.lean#L72-L98

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

theorem PI.WGB.stepA_cleared (k : ℕ) (hk : k < n) (y : Fin (n + 1) × Fin (n + 1) → ℂ)
    (hy : clearedA k y) (hp : y (⟨k, by omega⟩, ⟨k, by omega⟩) ≠ 0) :
    clearedA (k + 1) (stepA ⟨k, by omega⟩ ⟨k, by omega⟩ y) := by sorry
