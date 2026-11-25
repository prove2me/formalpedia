-- Prove2me | Theorems.Thm_PI_EF_norm_near_sum_le
-- name    : PI.EF.norm_near_sum_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:41.131359+00:00
-- url     : https://prove2.me/theorems/190556e2-d783-448a-b74f-395b49a5bd59
-- title:
--   EF: norm near sum le
-- statement:
--   The EF construction uses the norm near sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LogDerivBounds.lean#L18-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LogDerivBounds.lean#L18-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBounds
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
open Complex DirichletCharacter

theorem PI.EF.norm_near_sum_le {C : ℝ} (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) {d : ℝ} (hd : 0 < d)
    (h : ∀ ρ ∈ ZerosNear χ s.im, d ≤ ‖s - ρ‖) :
    ‖∑ᶠ ρ ∈ ZerosNear χ s.im, (mult χ ρ : ℂ) / (s - ρ)‖ ≤
      C * Real.log (N * (|s.im| + 2)) / d := by sorry
