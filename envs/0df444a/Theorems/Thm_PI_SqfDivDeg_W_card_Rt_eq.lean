-- Prove2me | Theorems.Thm_PI_SqfDivDeg_W_card_Rt_eq
-- name    : PI.SqfDivDeg.W.card_Rt_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:42.27284+00:00
-- url     : https://prove2.me/theorems/db75569c-3fa6-5102-9230-14d9871d6464
-- title:
--   W: card Rt eq
-- statement:
--   The W construction uses the card Rt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/CardMonicTwoRootsLe.lean#L111-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/CardMonicTwoRootsLe.lean#L111-L125

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_CardMonicTwoRootsLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W
open Classical

theorem PI.SqfDivDeg.W.card_Rt_eq {g : ℕ} [Fact g.Prime] (n : ℕ) :
    (Rt g n).card = ∑ f ∈ Mon g n, (if (rts f).card = 0 then 0 else 1) := by sorry
