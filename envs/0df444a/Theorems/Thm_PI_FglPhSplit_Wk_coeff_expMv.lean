-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_coeff_expMv
-- name    : PI.FglPhSplit.Wk.coeff_expMv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:49.781322+00:00
-- url     : https://prove2.me/theorems/a7fe969c-586a-4aba-a4e3-43afcdb09edd
-- title:
--   Wk: coeff exp Mv
-- statement:
--   The Wk construction uses the coeff exp Mv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/Development.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/Development.lean#L32-L34

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

theorem PI.FglPhSplit.Wk.coeff_expMv {K : Type} [Field K] {σ : Type} (f : MvPowerSeries σ K) (α : σ →₀ ℕ) :
    coeff α (expMv f) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1), coeff α (f ^ n) / (n.factorial : K) := by sorry
