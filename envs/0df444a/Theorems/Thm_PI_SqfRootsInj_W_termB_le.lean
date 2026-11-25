-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_termB_le
-- name    : PI.SqfRootsInj.W.termB_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:50.343799+00:00
-- url     : https://prove2.me/theorems/d7004ac0-aacd-52d0-a68d-5038a2c90334
-- title:
--   W: term B le
-- statement:
--   The W construction uses the term B le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/RpowQuarterPowFour.lean#L48-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/RpowQuarterPowFour.lean#L48-L68

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_SumSqPowLeTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_RpowQuarterPowFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab

theorem PI.SqfRootsInj.W.termB_le (g r e e' ℓ : ℕ) (s : ℝ) (hs0 : 0 < s) (hs4 : s ^ 4 = g)
    (hℓ : ℓ.Prime) (hB : ℓ ∉ BB r g) (he1 : 1 ≤ e) (hsum : e + e' ≤ r) :
    ((g ^ e' * Lp g e ℓ * g ^ (r - e - e') : ℕ) : ℝ) ≤ (g : ℝ) ^ r * (s⁻¹) ^ (3 * e) := by sorry
