-- Prove2me | Theorems.Thm_PI_EF_order_ne_top_of_entire
-- name    : PI.EF.order_ne_top_of_entire
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:52.672643+00:00
-- url     : https://prove2.me/theorems/14be3cd8-99ce-5b97-8b52-236a55181fd8
-- title:
--   EF: order ne top of entire
-- statement:
--   The EF construction uses the order ne top of entire property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructA.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructA.lean#L111-L117

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA
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
open Complex Filter Topology Set

theorem PI.EF.order_ne_top_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    (y : ℂ) : analyticOrderAt f y ≠ ⊤ := by sorry
