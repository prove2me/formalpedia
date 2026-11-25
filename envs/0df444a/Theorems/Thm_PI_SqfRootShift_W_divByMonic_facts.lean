-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_divByMonic_facts
-- name    : PI.SqfRootShift.W.divByMonic_facts
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:27:38.400829+00:00
-- url     : https://prove2.me/theorems/e26e6c4a-db79-4b32-b4f6-b615144dee0d
-- title:
--   W: div By Monic facts
-- statement:
--   The W construction uses the div By Monic facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountC.lean#L70-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountC.lean#L70-L81

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

theorem PI.SqfRootShift.W.divByMonic_facts {r : ℕ} {f P : (ZMod g)[X]} (hf : IsLab g r f) (hP : P.Monic)
    (hdvd : P ∣ f) :
    f = P * (f /ₘ P) ∧ (f /ₘ P).Monic ∧ (f /ₘ P).natDegree = r - P.natDegree := by sorry
