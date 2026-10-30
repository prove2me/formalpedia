-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch19_pentagonalIndex_of_neg
-- name    : QseriesFormalization.PartIV.Ch19.pentagonalIndex_of_neg
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:58:17.266977+00:00
-- url     : https://prove2.me/theorems/5fa0dd59-f744-4af1-aaac-33e9ec3618f3
-- title:
--   Pentagonal index for negative $j$
-- statement:
--   Define $\mathrm{pentagonalIndex}(j)=\lfloor j(3j+1)/2\rfloor$ as a natural number (for $j\in\mathbb{Z}$). For every negative integer $j$, writing $m=-j$,
--   $$\mathrm{pentagonalIndex}(j)=\frac{m(3m-1)}{2}$$
--   (with natural-number arithmetic). This gives the generalized pentagonal numbers of the form $m(3m-1)/2$ from the integer parametrization, in Chapter 19.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19_JacobiTripleSignChar.lean#L381-L399

import Definitions.Def_QseriesFormalization_Chapter19_JacobiTripleSignChar
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
open QseriesFormalization.PartIV
open QseriesFormalization.PartIV.Ch19

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

theorem QseriesFormalization.PartIV.Ch19.pentagonalIndex_of_neg (j : ℤ) (hj : j < 0) :
    pentagonalIndex j = (-j).toNat * (3 * (-j).toNat - 1) / 2 := by sorry
