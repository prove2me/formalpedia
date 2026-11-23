-- Prove2me | Theorems.Thm_P2M_PI_FglPhSplit_Wk_coeff_pow_eq_zero__60e911f4ed32
-- name    : P2M_PI_FglPhSplit_Wk_coeff_pow_eq_zero__60e911f4ed32
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:34.262816+00:00
-- url     : https://prove2.me/theorems/7fd074f4-b6db-4a7b-a397-9397807376d7
-- title:
--   P2 M PI Fgl Ph Split Wk coeff pow eq zero  60e911f4ed32: P2 M PI Fgl Ph Split Wk coeff pow eq zero  60e911f4ed32
-- statement:
--   The P2 M PI Fgl Ph Split Wk coeff pow eq zero  60e911f4ed32 construction uses the P2 M PI Fgl Ph Split Wk coeff pow eq zero  60e911f4ed32 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/AddPreservesExpCongruence.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/AddPreservesExpCongruence.lean#L47-L49

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

theorem P2M_PI_FglPhSplit_Wk_coeff_pow_eq_zero__60e911f4ed32 {f : MvPowerSeries σ K} (hf : constantCoeff f = 0) {n : ℕ}
    {α : σ →₀ ℕ} (h : Finsupp.degree α < n) : coeff α (f ^ n) = 0 := by sorry

alias «PI».«FglPhSplit».«Wk».«coeff_pow_eq_zero'» := P2M_PI_FglPhSplit_Wk_coeff_pow_eq_zero__60e911f4ed32
