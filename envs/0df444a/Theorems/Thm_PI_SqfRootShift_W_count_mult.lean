-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_count_mult
-- name    : PI.SqfRootShift.W.count_mult
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:12.208489+00:00
-- url     : https://prove2.me/theorems/ed9fbf22-3a48-4a5c-b652-2876ff7cb9df
-- title:
--   W: count mult
-- statement:
--   The W construction uses the count mult property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountC.lean#L85-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountC.lean#L85-L100

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

theorem PI.SqfRootShift.W.count_mult (r : ℕ) (T : Finset (ZMod g)[X]) (hT : ∀ f ∈ T, IsLab g r f)
    (P : (ZMod g)[X]) (hP : P.Monic) :
    (T.filter (fun f => P ∣ f)).card ≤ g ^ (r - P.natDegree) := by sorry
