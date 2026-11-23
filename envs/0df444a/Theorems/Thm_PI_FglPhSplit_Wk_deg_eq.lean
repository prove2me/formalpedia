-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_deg_eq
-- name    : PI.FglPhSplit.Wk.deg_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:46.069164+00:00
-- url     : https://prove2.me/theorems/1665d4c0-f467-432c-ad99-c9b339e11d6c
-- title:
--   Wk: deg eq
-- statement:
--   The Wk construction uses the deg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/AddPreservesExpCongruence.lean#L11-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/AddPreservesExpCongruence.lean#L11-L11

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

theorem PI.FglPhSplit.Wk.deg_eq (α : σ →₀ ℕ) : (α.sum fun _ k => k) = Finsupp.degree α := by sorry
