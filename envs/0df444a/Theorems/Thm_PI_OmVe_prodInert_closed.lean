-- Prove2me | Theorems.Thm_PI_OmVe_prodInert_closed
-- name    : PI.OmVe.prodInert_closed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:32.031911+00:00
-- url     : https://prove2.me/theorems/03b347cc-73d3-592a-ab8c-b04bdbc47d7c
-- title:
--   Om Ve: prod Inert closed
-- statement:
--   The Om Ve construction uses the prod Inert closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/ProdInertClosed.lean#L28-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/ProdInertClosed.lean#L28-L53

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

theorem PI.OmVe.prodInert_closed (x : ℝ) (hx : x ≠ 0) (M : ℕ) : ∀ a, a ≤ M →
    ∏ j : Fin a, (x ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * x ^ (M - j - 1)) =
      x ^ (2 * M * a - a ^ 2) * ∏ j ∈ Finset.Icc (M - a + 1) M, (1 - (-1) ^ j * x ^ (-(j : ℤ))) := by sorry
