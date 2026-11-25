-- Prove2me | Theorems.Thm_PI_OmVe_prodSplit_closed
-- name    : PI.OmVe.prodSplit_closed
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:50.137919+00:00
-- url     : https://prove2.me/theorems/ee1ec569-dd02-4b39-8fd3-8c70d2d7ee7c
-- title:
--   Om Ve: prod Split closed
-- statement:
--   The Om Ve construction uses the prod Split closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/ProdInertClosed.lean#L7-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/ProdInertClosed.lean#L7-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_ProdInertClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmVe

theorem PI.OmVe.prodSplit_closed (x : ℝ) (hx : x ≠ 0) (M : ℕ) : ∀ a, a ≤ M →
    ∏ i : Fin a, (x ^ M - x ^ (i : ℕ)) = x ^ (M * a) * ∏ j ∈ Finset.Icc (M - a + 1) M, (1 - x ^ (-(j : ℤ))) := by sorry
