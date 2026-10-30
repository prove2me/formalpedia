-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch19_pentagonalSign_mem
-- name    : QseriesFormalization.PartIV.Ch19.pentagonalSign_mem
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:58:21.441647+00:00
-- url     : https://prove2.me/theorems/ed28944f-c484-4677-97b9-a5d455b3ba79
-- title:
--   The pentagonal sign takes only the values $-1,0,1$
-- statement:
--   For every natural number $n$, $\mathrm{pentagonalSign}(n)\in\{-1,0,1\}$, where $\mathrm{pentagonalSign}(n)=(-1)^k$ if $n=k(3k\mp1)/2$ is a generalized pentagonal number and $0$ otherwise. Equivalently every coefficient of $\prod(1-q^i)$ is $-1$, $0$ or $1$ (Chapter 19).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19_JacobiTripleSignChar.lean#L250-L264

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

theorem QseriesFormalization.PartIV.Ch19.pentagonalSign_mem (n : ℕ) :
    pentagonalSign n = -1 ∨ pentagonalSign n = 0 ∨ pentagonalSign n = 1 := by sorry
