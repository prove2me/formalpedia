-- Prove2me | Theorems.Thm_P2M_PI_SqfRootsInj_W_pow_pred_eq_one__d29b6a46da77
-- name    : P2M_PI_SqfRootsInj_W_pow_pred_eq_one__d29b6a46da77
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:04.470289+00:00
-- url     : https://prove2.me/theorems/c895d474-1c3a-4050-b5ea-02388f5ea84b
-- title:
--   P2 M PI Sqf Roots Inj W pow pred eq one  d29b6a46da77: P2 M PI Sqf Roots Inj W pow pred eq one  d29b6a46da77
-- statement:
--   The P2 M PI Sqf Roots Inj W pow pred eq one  d29b6a46da77 construction uses the P2 M PI Sqf Roots Inj W pow pred eq one  d29b6a46da77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/WitMain.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/WitMain.lean#L36-L39

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

theorem P2M_PI_SqfRootsInj_W_pow_pred_eq_one__d29b6a46da77 {K : Type*} [Field K] {x : K} (hx : x ≠ 0) {q : ℕ} (hq : 1 ≤ q)
    (h : x ^ q = x) : x ^ (q - 1) = 1 := by sorry

alias «PI».«SqfRootsInj».«W».«pow_pred_eq_one'» := P2M_PI_SqfRootsInj_W_pow_pred_eq_one__d29b6a46da77
