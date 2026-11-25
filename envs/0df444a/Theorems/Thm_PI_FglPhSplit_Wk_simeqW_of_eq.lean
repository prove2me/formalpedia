-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_simeqW_of_eq
-- name    : PI.FglPhSplit.Wk.simeqW_of_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:56.18583+00:00
-- url     : https://prove2.me/theorems/2bd76604-dbb6-403e-ac2e-a828663617f1
-- title:
--   Wk: simeq W of eq
-- statement:
--   The Wk construction uses the simeq W of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/Development.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/Development.lean#L49-L52

import Definitions.Def_Formalism_PeriodIntegrals_FglPhSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
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
open PI.FglPhSplit MvPowerSeries

theorem PI.FglPhSplit.Wk.simeqW_of_eq {K : Type} [Field K] {W : Subring K} {σ : Type} {f g f' g' : MvPowerSeries σ K}
    (h : SimeqW W f g) (hf : f = f') (hg : g = g') : SimeqW W f' g' := by sorry
