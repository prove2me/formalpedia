-- Prove2me | Theorems.Thm_SensitivityActualLowPopulations_budget_eq_sum
-- name    : SensitivityActualLowPopulations.budget_eq_sum
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:16.647803+00:00
-- url     : https://prove2.me/theorems/77b96f41-6e65-4334-ad0f-12f54f045cc4
-- title:
--   Cumulative low-population budget equals the actual guard sum
-- statement:
--   For any finite candidate set, natural-valued guard count, and q in Fin 4, the budget computed from the exact-count population vector equals the sum of the guard counts of candidates whose count is at most q.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/ActualLowPopulations.lean lines 51–67; SHA256 d35ce783f26ec323d60b57d38df5139dc0b171fbdfafd1ff8b980a54e3c80a43; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActualLowPopulations
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PairedPopulationConstraints
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityActualLowPopulations
end SensitivityActualLowPopulations
namespace SensitivityOperativeHeads
end SensitivityOperativeHeads
namespace SensitivityPairedPopulation
end SensitivityPairedPopulation
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! The four integer population variables are exact counts of actual
operative low rows. Their prefixes and spent budgets equal the sets and
finite sums used by the semantic graph inequalities. -/
open SensitivityActualLowPopulations
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityOperativeHeads SensitivityPairedPopulation
set_option autoImplicit false
variable {V S I Color : Type} {L : ℕ}

theorem SensitivityActualLowPopulations.budget_eq_sum (candidates : Finset V) (count : V → ℕ) (q : Fin 4) :
    budget (population candidates count) q =
      ∑ v ∈ candidates.filter (fun v => count v ≤ q.val), count v := by sorry
