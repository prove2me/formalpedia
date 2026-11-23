-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_coeff_expT
-- name    : PI.FglPhSplit.Wk.coeff_expT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:58.565969+00:00
-- url     : https://prove2.me/theorems/886818ef-d951-4a9d-926b-f43d1fc5a851
-- title:
--   Wk: coeff exp T
-- statement:
--   The Wk construction uses the coeff exp T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/AddPreservesExpCongruence.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/AddPreservesExpCongruence.lean#L54-L58

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

theorem PI.FglPhSplit.Wk.coeff_expT (f : MvPowerSeries σ K) (N : ℕ) (α : σ →₀ ℕ) :
    coeff α (expT f N) = ∑ n ∈ range N, coeff α (f ^ n) / (n.factorial : K) := by sorry
