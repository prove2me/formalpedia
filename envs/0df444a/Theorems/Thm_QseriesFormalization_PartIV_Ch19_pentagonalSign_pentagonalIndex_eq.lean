-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch19_pentagonalSign_pentagonalIndex_eq
-- name    : QseriesFormalization.PartIV.Ch19.pentagonalSign_pentagonalIndex_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:58:55.601987+00:00
-- url     : https://prove2.me/theorems/57f4680f-7d58-47aa-9200-ac3cff0bcf28
-- title:
--   The pentagonal sign at $\mathrm{pentagonalIndex}(j)$ is $(-1)^{|j|}$
-- statement:
--   For every integer $j$, with $\mathrm{pentagonalIndex}(j)=\lfloor j(3j+1)/2\rfloor$ and $\mathrm{pentagonalSign}(n)$ the coefficient of $q^n$ in $\prod(1-q^i)$ (that is $(-1)^k$ if $n=k(3k\mp1)/2$, and $0$ otherwise),
--   $$\mathrm{pentagonalSign}(\mathrm{pentagonalIndex}(j))=(-1)^{|j|}.$$
--   This bridges the integer-indexed form of the pentagonal number theorem, $\sum_{j\in\mathbb{Z}}(-1)^jq^{j(3j+1)/2}$, and the natural-number-indexed series (Chapter 19).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19_JacobiTripleSignChar.lean#L644-L670

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

theorem QseriesFormalization.PartIV.Ch19.pentagonalSign_pentagonalIndex_eq (j : ℤ) :
    pentagonalSign (pentagonalIndex j) = (-1 : ℤ)^j.natAbs := by sorry
