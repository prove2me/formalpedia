-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_orderOf_dvd_pow_sub_one
-- name    : PI.SqfRootsInj.W.orderOf_dvd_pow_sub_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:00.776227+00:00
-- url     : https://prove2.me/theorems/6ec49d61-a456-47cd-8a31-83486446efe1
-- title:
--   W: order Of dvd pow sub one
-- statement:
--   The W construction uses the order Of dvd pow sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/WitMain.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/WitMain.lean#L50-L56

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

theorem PI.SqfRootsInj.W.orderOf_dvd_pow_sub_one {x : Fbar g} (hx0 : x ≠ 0) {e : ℕ}
    (he : (minpoly (ZMod g) x).natDegree = e) (he1 : 1 ≤ e) :
    g ^ e - 1 ≠ 0 ∧ orderOf x ∣ g ^ e - 1 := by sorry
