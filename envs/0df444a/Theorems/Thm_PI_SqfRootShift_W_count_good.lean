-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_count_good
-- name    : PI.SqfRootShift.W.count_good
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:29.789717+00:00
-- url     : https://prove2.me/theorems/ad52663a-207c-44c5-9f93-c9739b5d3641
-- title:
--   W: count good
-- statement:
--   The W construction uses the count good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountC.lean#L15-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountC.lean#L15-L57

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountC
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
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
open Classical

theorem PI.SqfRootShift.W.count_good (c : (ZMod g)ˣ) (hg : 3 ≤ g) (k : ℕ) (hk : 1 ≤ k)
    (Q : Finset (ZMod g)[X]) (hQ : ∀ P ∈ Q, Good c P ∧ P.natDegree = k) :
    k * Q.card ≤ ppSum (g ^ k - 1) := by sorry
