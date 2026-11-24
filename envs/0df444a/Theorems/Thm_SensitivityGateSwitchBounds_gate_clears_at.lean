-- Prove2me | Theorems.Thm_SensitivityGateSwitchBounds_gate_clears_at
-- name    : SensitivityGateSwitchBounds.gate_clears_at
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:48:48.958125+00:00
-- url     : https://prove2.me/theorems/3e69d8e2-a6cf-4a80-a703-767bc657c208
-- title:
--   Acceptance forces forbidden guards to be quiet
-- statement:
--   Suppose the recipe at rank $j$ forbids guard activity at cutoff $a$: either its soft allowance is zero and its soft cutoff is at most $a$, or its hard cutoff is at most $a$. For a nested child family,
--   $$
--   G_v(j,x)\quad\Longrightarrow\quad
--   \forall Q\in\mathcal G(v),\;Q\text{ is inactive at }a.
--   $$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/GateSwitchBounds.lean lines 26–43; SHA256 804ec6f1d7d467e7f7109cc54706c22f4f6569ca97a4a12a476dda1116971747; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_GateSwitchBounds
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityGateSwitchBounds
end SensitivityGateSwitchBounds
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivitySocketEventSupport
end SensitivitySocketEventSupport
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates


/-!
Strict identity switches between different parent rows are supported on one
child socket selected by a separating guard. In the lowering orientation the
child B profile pays for the event. In the raising orientation the unary A
profile suffices, while an unchanged paired mate fixes the child color and
permits the sharper C profile.
-/
open SensitivityGateSwitchBounds
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityStrictGateStates SensitivitySocketEventSupport
variable {V S I Color : Type} {L core : ℕ}

theorem SensitivityGateSwitchBounds.gate_clears_at {row : RowFamily I Color L} (hnested : Nested row)
    (guards : GuardFamily V S) (recipe : GateRecipe S L)
    (v : V) (j cutoff : Fin L) (hforbid : ForbidsAt recipe j cutoff)
    (x : ((V × S) × I) → Bool) (hrow : gateRow row guards recipe v j x) :
    ∀ check ∈ guards v, ¬ guardActive row cutoff.val x check := by sorry
