-- Prove2me | Theorems.Thm_SensitivityHeadSocketCharges_pair_three_charges
-- name    : SensitivityHeadSocketCharges.pair_three_charges
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:10.404488+00:00
-- url     : https://prove2.me/theorems/3eb82d6a-ff72-497e-9c4a-455acd757b97
-- title:
--   Three incoming-hit prices bound two socket unions
-- statement:
--   Let each of two sockets have an own event set and an incoming event set, with scaled own and union bounds. If hits is at most two, zero hits forces both incoming sets empty, and at most one hit leaves one incoming side empty, then the three coefficient inequalities for hits 0, 1, and 2 imply that the sum of both union cardinalities is at most scale·cf[3·kind+hits].
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/HeadPairNumericCharges.lean lines 13–46; SHA256 ea4ae852c8ddaa450990590e7c295f0121904cea0d31f48b5431ce42effc5dfa; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
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
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityHeadSocketCharges
end SensitivityHeadSocketCharges


/-! The three source coefficients correspond to no incoming macro, one
incoming macro, or at least two incoming macros at a paired high head. -/
open SensitivityHeadSocketCharges
open scoped Classical BigOperators
set_option autoImplicit false
variable {I : Type} [Fintype I]

theorem SensitivityHeadSocketCharges.pair_three_charges (scale : ℝ) (hscale : 0 ≤ scale)
    (own incoming : Bool → Finset I) (base combined : Bool → ℕ)
    (kind hits : ℕ) (hhits : hits ≤ 2) (cf : Array ℕ)
    (hbase : ∀ side, ((own side).card : ℝ) ≤ scale * (base side : ℕ))
    (hcombined : ∀ side, ((own side ∪ incoming side).card : ℝ) ≤ scale * (combined side : ℕ))
    (hzero : hits = 0 → ∀ side, incoming side = ∅)
    (hone : hits ≤ 1 → ∃ side, incoming (!side) = ∅)
    (hcf0 : base false + base true ≤ cf[3*kind]?.getD 0)
    (hcf1 : max (combined false + base true) (base false + combined true) ≤ cf[3*kind+1]?.getD 0)
    (hcf2 : combined false + combined true ≤ cf[3*kind+2]?.getD 0) :
    (∑ side : Bool, ((own side ∪ incoming side).card : ℝ)) ≤
      scale * (cf[3*kind+hits]?.getD 0 : ℕ) := by sorry
