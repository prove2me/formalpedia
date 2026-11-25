-- Prove2me | Theorems.Thm_PI_EF_card_le_sum_mult
-- name    : PI.EF.card_le_sum_mult
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:49.636974+00:00
-- url     : https://prove2.me/theorems/d39cf3c1-41bb-4e6a-91ed-d4280e379125
-- title:
--   EF: card le sum mult
-- statement:
--   The EF construction uses the card le sum mult property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L123-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeight.lean#L123-L130

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

theorem PI.EF.card_le_sum_mult {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (B : Finset ℂ)
    (hB : ∀ ρ ∈ B, ρ.re < 1 ∧ LFunction χ ρ = 0) :
    (B.card : ℝ) ≤ ∑ ρ ∈ B, (mult χ ρ : ℝ) := by sorry
