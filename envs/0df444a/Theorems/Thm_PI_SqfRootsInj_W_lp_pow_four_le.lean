-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_lp_pow_four_le
-- name    : PI.SqfRootsInj.W.lp_pow_four_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:26.201629+00:00
-- url     : https://prove2.me/theorems/d6bd33fc-3ba3-4521-8729-312d749aa093
-- title:
--   W: lp pow four le
-- statement:
--   The W construction uses the lp pow four le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/TwoPowCardPrimeFactorsLe.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/TwoPowCardPrimeFactorsLe.lean#L13-L21

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_ClaimOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_TwoPowCardPrimeFactorsLe
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

theorem PI.SqfRootsInj.W.lp_pow_four_le {g r e ℓ : ℕ} (hℓ : ℓ.Prime) (hB : ℓ ∉ BB r g) (h1 : 1 ≤ e)
    (h2 : e ≤ r) : (Lp g e ℓ) ^ 4 ≤ g ^ e := by sorry
