-- Prove2me | Theorems.Thm_PI_EF_exists_good_height
-- name    : PI.EF.exists_good_height
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:44.294883+00:00
-- url     : https://prove2.me/theorems/b36f783d-5e28-4b17-a485-87f56c974f2c
-- title:
--   EF: exists good height
-- statement:
--   The EF construction uses the exists good height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L161-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L161-L210

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

theorem PI.EF.exists_good_height {C : ℝ} (hC0 : 0 ≤ C) (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T) :
    ∃ T' ∈ Set.Icc T (T + 1), ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → LFunction χ ρ = 0 →
      1 / (2 * (2 * C * Real.log (N * (T + 3)) + 1)) ≤ |(|ρ.im|) - T'| := by sorry
