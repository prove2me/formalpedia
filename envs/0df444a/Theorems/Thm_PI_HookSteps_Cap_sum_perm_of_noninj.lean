-- Prove2me | Theorems.Thm_PI_HookSteps_Cap_sum_perm_of_noninj
-- name    : PI.HookSteps.Cap.sum_perm_of_noninj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:12.379831+00:00
-- url     : https://prove2.me/theorems/a3578f0f-4f88-41c8-952c-c337ae3ceae7
-- title:
--   Cap: sum perm of noninj
-- statement:
--   The Cap construction uses the sum perm of noninj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliOps.lean#L70-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/CapelliOps.lean#L70-L81

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.HookSteps PI.HookSteps.Cap
open MvPolynomial Finset

theorem PI.HookSteps.Cap.sum_perm_of_noninj {M : Type} [AddCommMonoid M] (N : ℕ) (F : (Fin N → Fin N) → M)
    (hF : ∀ s, ¬ Function.Injective s → F s = 0) :
    ∑ s, F s = ∑ π : Equiv.Perm (Fin N), F π := by sorry
