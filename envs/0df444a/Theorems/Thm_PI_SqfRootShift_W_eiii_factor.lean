-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_eiii_factor
-- name    : PI.SqfRootShift.W.eiii_factor
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:27:39.529085+00:00
-- url     : https://prove2.me/theorems/ecfd5108-d000-5fb0-9034-d3d87408e02a
-- title:
--   W: eiii factor
-- statement:
--   The W construction uses the eiii factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountD.lean#L11-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountD.lean#L11-L49

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountD
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

theorem PI.SqfRootShift.W.eiii_factor {g : ℕ} [Fact g.Prime] {r : ℕ} (c : (ZMod g)ˣ) {f : (ZMod g)[X]}
    (hf : Eiii g r c f) :
    ∃ P, Good c P ∧ P ∣ f ∧ 1 ≤ P.natDegree ∧ P.natDegree ≤ r := by sorry
