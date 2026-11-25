-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_simeqW_add
-- name    : PI.FglPhSplit.Wk.simeqW_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:47.048804+00:00
-- url     : https://prove2.me/theorems/8e7d90e3-4aaa-5fe1-adea-c553c38453c0
-- title:
--   Wk: simeq W add
-- statement:
--   The Wk construction uses the simeq W add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/AddPreservesExpCongruence.lean#L134-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/AddPreservesExpCongruence.lean#L134-L142

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPhSplit PI.FglPhSplit.Wk
open PI.FglPhSplit MvPowerSeries Finset
variable {K : Type} [Field K] {σ : Type}

theorem PI.FglPhSplit.Wk.simeqW_add [CharZero K] {W : Subring K} {f g f' g' : MvPowerSeries σ K}
    (h : SimeqW W f g) (h' : SimeqW W f' g') : SimeqW W (f + f') (g + g') := by sorry
