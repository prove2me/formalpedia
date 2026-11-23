-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_root_facts
-- name    : PI.SqfRootsInj.W.root_facts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:46.690206+00:00
-- url     : https://prove2.me/theorems/eec8f8f5-db29-4cb1-9a02-a7edb689049e
-- title:
--   W: root facts
-- statement:
--   The W construction uses the root facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/WitMain.lean#L14-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/WitMain.lean#L14-L34

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitMain
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
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]

theorem PI.SqfRootsInj.W.root_facts {r : ℕ} {f : (ZMod g)[X]} (hf : IsLab g r f) {x : Fbar g}
    (hx : x ∈ rootsBar f) :
    x ≠ 0 ∧ minpoly (ZMod g) x ∣ f ∧ (minpoly (ZMod g) x).natDegree ≤ r ∧
      1 ≤ (minpoly (ZMod g) x).natDegree := by sorry
