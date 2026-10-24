-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch19_no_minus_pentagonal_eq_plus_pentagonal
-- name    : QseriesFormalization.PartIV.Ch19.no_minus_pentagonal_eq_plus_pentagonal
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:56:44.373103+00:00
-- url     : https://prove2.me/theorems/4c65486f-cae7-4481-8a50-4b693768358e
-- title:
--   No $k(3k-1)/2$ equals $j(3j+1)/2$ for $j>0$
-- statement:
--   For every natural number $j>0$ and every natural number $k$, $k(3k-1)/2\ne j(3j+1)/2$ (with natural-number arithmetic). Equivalently the two families of generalized pentagonal numbers $k(3k-1)/2$ and $j(3j+1)/2$ ($j\ge 1$) never coincide. This is used in Chapter 19 to show that the pentagonal sign is well defined as a function of the index.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19_JacobiTripleSignChar.lean#L488 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_Chapter05_Franklin
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Characterisation of `jacobiTripleSign`

Two clean closed forms for `jacobiTripleSign` (defined in `Chapter19.lean`
via `List.find?` on triangular indices):

* `jacobiTripleSign_triangular`: `jacobiTripleSign (k*(k+1)/2) = (-1)^k * (2k+1)`.
* `jacobiTripleSign_of_not_triangular`: `jacobiTripleSign n = 0` when no
  `k ≤ n` satisfies `n = k*(k+1)/2`.

These will be needed by both attack routes on the cube convolution
identity (Sylvester combinatorial proof in `Pending/Sylvester_TripleSum`
and the analytic-formal Taylor bridge in `Pending/JacobiCubeAnalyticToFormal`).
Stating them in the main build (rather than inside a Pending file)
keeps the headline target portable.
-/

open QseriesFormalization

/-! ### Analogous lemmas for `pentagonalSign` (parallels jacobiTripleSign).

For the analytic→formal bridge on the LHS of the cube identity, we also
need bounds and summability for `(pentagonalSign n : ℂ) * q^n`. -/

open QseriesFormalization.PartI.Ch04Franklin (pentagonalSign)

/-! ### Pentagonal index function and its injectivity.

For the analytic Euler pentagonal identity in `ℕ`-indexed form, we use
the map `j ↦ j*(3j+1)/2 : ℤ → ℕ` which sends integers to pentagonal
numbers (both `+` and `-` branches).  The map is injective.

This is the bridge from Ch04's bilateral `ℤ`-indexed analytic identity
to the `ℕ`-indexed formal-Taylor form needed for the cube argument. -/

theorem QseriesFormalization.PartIV.Ch19.no_minus_pentagonal_eq_plus_pentagonal (j : ℕ) (hj : 0 < j) :
    ∀ k : ℕ, k * (3 * k - 1) / 2 ≠ j * (3 * j + 1) / 2 := by sorry
