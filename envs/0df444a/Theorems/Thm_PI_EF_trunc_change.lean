-- Prove2me | Theorems.Thm_PI_EF_trunc_change
-- name    : PI.EF.trunc_change
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:06.335856+00:00
-- url     : https://prove2.me/theorems/5127218b-cc72-4c66-bf4f-953278df6e34
-- title:
--   EF: trunc change
-- statement:
--   The EF construction uses the trunc change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L212-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L212-L267

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

theorem PI.EF.trunc_change {C : ℝ} (hC0 : 0 ≤ C) (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {T T' u : ℝ} (hT : 0 < T)
    (hT' : T' ∈ Set.Icc T (T + 1)) (hu : 1 ≤ u) :
    ‖(∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) -
        ∑ᶠ ρ ∈ ZerosBelow χ T, (mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
      2 * C * Real.log (N * (T + 3)) * (u / T) := by sorry
