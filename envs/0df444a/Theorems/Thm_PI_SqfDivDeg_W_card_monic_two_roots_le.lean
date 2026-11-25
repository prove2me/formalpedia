-- Prove2me | Theorems.Thm_PI_SqfDivDeg_W_card_monic_two_roots_le
-- name    : PI.SqfDivDeg.W.card_monic_two_roots_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:24:52.866562+00:00
-- url     : https://prove2.me/theorems/15a0272d-24ed-4db5-987b-c076b13ba716
-- title:
--   W: card monic two roots le
-- statement:
--   The W construction uses the card monic two roots le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/CardMonicTwoRootsLe.lean#L51-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/CardMonicTwoRootsLe.lean#L51-L79

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

theorem PI.SqfDivDeg.W.card_monic_two_roots_le {g : ℕ} [Fact g.Prime] (n : ℕ) (c d : ZMod g) (hcd : c ≠ d) :
    ((Mon g (n + 2)).filter (fun f => f.IsRoot c ∧ f.IsRoot d)).card ≤ g ^ n := by sorry
