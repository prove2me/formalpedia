-- Prove2me | Theorems.Thm_SensitivityStrictGateStates_gateRow_iff_weightCount
-- name    : SensitivityStrictGateStates.gateRow_iff_weightCount
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:50:43.65473+00:00
-- url     : https://prove2.me/theorems/80c13856-7bd3-4bd5-a2de-31ab805af6d4
-- title:
--   Scalar weighted-state semantics of a strict gate
-- statement:
--   For a nested child family and a strict guard-shape recipe, row $v$ accepts rank $j$ exactly when its weighted guard count $W$ is at most one and there is a color and an allowed matching target assignment at count $W$:
--   $$
--   G_v(j,x)\iff
--   W\le1\ \land\
--   \exists c,\alpha\in\mathrm{targets}(j,W),\
--   \forall s,\ F_{c,\alpha(s)}(x_{v,s}).
--   $$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/StrictGateStates.lean lines 105–123; SHA256 8a707cceb665a7f88c56310be7495b8933682225933379f4c87f2becce290cbf; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_StrictGateStates
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

namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates
namespace SensitivityTargetEvents
end SensitivityTargetEvents


/-!
Exact finite-state semantics for the strict rows in the P/J recurrences.
Ordinary strict rows have zero tolerance and a disabled hard cutoff; warm
strict rows have allowance one and a finite hard cutoff. Both are represented
by the source's sum of two indicator weights, with legal total at most one.
-/
open SensitivityStrictGateStates
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityFiniteRanks SensitivityTargetEvents
set_option autoImplicit false
variable {I Color V S : Type} {L : ℕ}

theorem SensitivityStrictGateStates.gateRow_iff_weightCount {row : RowFamily I Color L} (hnested : Nested row)
    (guards : GuardFamily V S) (recipe : GateRecipe S L) (v : V) (j : Fin L)
    (hshape : StrictGuardShape recipe j) (x : ((V × S) × I) → Bool) :
    gateRow row guards recipe v j x ↔
      weightCount row guards recipe v j x ≤ 1 ∧
      ∃ c assignment, assignment ∈ recipe.targets j (weightCount row guards recipe v j x) ∧
        ∀ s, row c (assignment s) (socketInput x (v,s)) := by sorry
