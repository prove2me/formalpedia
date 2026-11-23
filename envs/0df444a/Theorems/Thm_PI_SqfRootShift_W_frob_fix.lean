-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_frob_fix
-- name    : PI.SqfRootShift.W.frob_fix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:31.854056+00:00
-- url     : https://prove2.me/theorems/c2e88994-6071-41a5-8166-08a7a9e7b469
-- title:
--   W: frob fix
-- statement:
--   The W construction uses the frob fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountB.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountB.lean#L13-L28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountB
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

theorem PI.SqfRootShift.W.frob_fix (x : Fbar g) :
    x ^ (g ^ (minpoly (ZMod g) x).natDegree) = x := by sorry
