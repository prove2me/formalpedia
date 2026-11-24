-- Prove2me | Theorems.Thm_SensitivityLocalNumericGateBridge_gateRow_congr_recipe_at
-- name    : SensitivityLocalNumericGateBridge.gateRow_congr_recipe_at
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:49:00.309526+00:00
-- url     : https://prove2.me/theorems/8b230233-6347-4e88-bca1-e679ebda4753
-- title:
--   Gate acceptance depends only on permitted recipe entries
-- statement:
--   Fix a rank $j$. If two recipes agree there on their soft cutoff, hard cutoff, and failure allowance, and agree on their target-assignment sets for every permitted failure count $f$, then for every child family, guard family, row $v$, and input $x$,
--   $$
--   G^{(1)}_v(j,x)\iff G^{(2)}_v(j,x).
--   $$
--   Target entries at failure counts exceeding the allowance need not agree.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/LocalNumericGateBridge.lean lines 13–33; SHA256 38ad83a478cce1add8f4e1dad1102b41ae3d86bb958a2139e7577a4ed21ca2e8; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityLocalConfigurationCoverage
end SensitivityLocalConfigurationCoverage
namespace SensitivityLocalNumeric
end SensitivityLocalNumeric
namespace SensitivityLocalNumericGateBridge
end SensitivityLocalNumericGateBridge
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankMapCheckpoint
end SensitivityRankMapCheckpoint
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! The truncated numeric targets agree with the actual gates at every
strict rank. No equality of the loose-rank predicates is asserted. -/
open SensitivityLocalNumericGateBridge
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
variable {V S I Color : Type} {L core : ℕ}

theorem SensitivityLocalNumericGateBridge.gateRow_congr_recipe_at
    (row : RowFamily I Color L) (guards : GuardFamily V S)
    (first second : GateRecipe S L) (j : Fin L)
    (hsoft : first.soft j = second.soft j) (hhard : first.hard j = second.hard j)
    (hallow : first.allowance j = second.allowance j)
    (htarget : ∀ f, f ≤ first.allowance j → first.targets j f = second.targets j f)
    (v : V) (x : ((V × S) × I) → Bool) :
    gateRow row guards first v j x ↔ gateRow row guards second v j x := by sorry
