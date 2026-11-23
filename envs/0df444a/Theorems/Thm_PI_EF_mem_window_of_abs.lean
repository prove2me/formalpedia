-- Prove2me | Theorems.Thm_PI_EF_mem_window_of_abs
-- name    : PI.EF.mem_window_of_abs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:28.514906+00:00
-- url     : https://prove2.me/theorems/77242a61-a5cd-4e76-95d9-d97f523585a2
-- title:
--   EF: mem window of abs
-- statement:
--   The EF construction uses the mem window of abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L148-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L148-L159

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open DirichletCharacter

theorem PI.EF.mem_window_of_abs {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {ρ : ℂ} {t : ℝ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hL : LFunction χ ρ = 0) (h : |(|ρ.im|) - t| ≤ 1) :
    ρ ∈ ZerosNear χ t ∪ ZerosNear χ (-t) := by sorry
