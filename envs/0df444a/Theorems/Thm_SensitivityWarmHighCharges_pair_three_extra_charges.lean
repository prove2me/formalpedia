-- Prove2me | Theorems.Thm_SensitivityWarmHighCharges_pair_three_extra_charges
-- name    : SensitivityWarmHighCharges.pair_three_extra_charges
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:22.056546+00:00
-- url     : https://prove2.me/theorems/cb27ecc9-a8c7-4bfa-8367-1dbe682e9d00
-- title:
--   Three hit prices combine a base cost with two incoming sides
-- statement:
--   Let the own events on two sockets together with an extra event set have scaled cost at most base, and let the incoming sides have costs left and right. If hits ≤ 2, zero hits empties both incoming sets, and at most one hit empties one side, then the inequalities base ≤ cf₀, base+max(left,right) ≤ cf₁, and base+left+right ≤ cf₂ bound the full two union sets plus extra by scale·cf[3·kind+hits].
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/WarmHighCharges.lean lines 13–62; SHA256 8c8407173183f34837d82a05aaa0fa4a8eff9224be284ba4384bab631bacb537; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityWarmHighCharges
end SensitivityWarmHighCharges


/-! Zero, one, or two receiving physical children add zero, one maximum,
or two downward prices to a warm head's own and soft-guard base price. -/
open SensitivityWarmHighCharges
open scoped Classical BigOperators
set_option autoImplicit false

theorem SensitivityWarmHighCharges.pair_three_extra_charges {I J : Type} [DecidableEq I]
    (scale : ℝ) (hscale : 0 ≤ scale) (own incoming : Bool → Finset I) (extra : Finset J)
    (base left right kind hits : ℕ) (hhits : hits ≤ 2) (cf : Array ℕ)
    (hbase : (∑ side : Bool, ((own side).card : ℝ)) + (extra.card : ℝ) ≤ scale*(base : ℕ))
    (hleft : ((incoming false).card : ℝ) ≤ scale*(left : ℕ))
    (hright : ((incoming true).card : ℝ) ≤ scale*(right : ℕ))
    (hzero : hits = 0 → ∀ side, incoming side = ∅)
    (hone : hits ≤ 1 → ∃ side : Bool, incoming (!side) = ∅)
    (hc0 : base ≤ cf[3*kind]?.getD 0)
    (hc1 : base + max left right ≤ cf[3*kind+1]?.getD 0)
    (hc2 : base + left + right ≤ cf[3*kind+2]?.getD 0) :
    (∑ side : Bool, ((own side ∪ incoming side).card : ℝ)) + (extra.card : ℝ) ≤
      scale*(cf[3*kind+hits]?.getD 0 : ℕ) := by sorry
