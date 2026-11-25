-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_termA_le
-- name    : PI.SqfRootsInj.W.termA_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:55.480006+00:00
-- url     : https://prove2.me/theorems/a1e060fa-f110-5bb4-bd01-943e10ad9f7a
-- title:
--   W: term A le
-- statement:
--   The W construction uses the term A le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/RpowQuarterPowFour.lean#L20-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/RpowQuarterPowFour.lean#L20-L46

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

theorem PI.SqfRootsInj.W.termA_le (g r e j ℓ : ℕ) (s : ℝ) (hs0 : 0 < s) (hs1 : 1 ≤ s) (hs4 : s ^ 4 = g)
    (hℓ : ℓ.Prime) (hB : ℓ ∉ BB r g) (he1 : 1 ≤ e) (her : e ≤ r) (hj : 2 * j ≤ e) :
    (((g ^ j - 1) * Lp g e ℓ * g ^ (r - e) : ℕ) : ℝ) ≤ (g : ℝ) ^ r * (s⁻¹) ^ e := by sorry
