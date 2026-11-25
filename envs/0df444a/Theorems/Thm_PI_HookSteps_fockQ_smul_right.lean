-- Prove2me | Theorems.Thm_PI_HookSteps_fockQ_smul_right
-- name    : PI.HookSteps.fockQ_smul_right
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:18.640376+00:00
-- url     : https://prove2.me/theorems/9056a46a-291d-4f64-8b89-f0e3acd0c8c3
-- title:
--   Hook Steps: fock Q smul right
-- statement:
--   The Hook Steps construction uses the fock Q smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DetShift.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DetShift.lean#L68-L72

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps
variable {N : ℕ}

theorem PI.HookSteps.fockQ_smul_right {σ : Type*} (c : ℚ) (f g : MvPolynomial σ ℚ) :
    fockQ f (c • g) = c * fockQ f g := by sorry
