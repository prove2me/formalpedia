-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch19_tsum_jacobiTripleSign_eq_jacobi_series
-- name    : QseriesFormalization.PartIV.Ch19.tsum_jacobiTripleSign_eq_jacobi_series
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T10:01:26.418746+00:00
-- url     : https://prove2.me/theorems/6dadb6b4-2cf8-466c-89d7-88c5cdbabb94
-- title:
--   Reindexing the Jacobi series: Taylor form equals triangular form
-- statement:
--   For every complex number $q$ (no convergence hypothesis; Lean's `tsum` is $0$ for non-summable families),
--   $$\sum_{k\ge0}\mathrm{jacobiTripleSign}(k)\,q^k=\sum_{n\ge0}(-1)^n(2n+1)\,q^{n(n+1)/2},$$
--   where $\mathrm{jacobiTripleSign}(k)=(-1)^n(2n+1)$ if $k=n(n+1)/2$ and $0$ otherwise. Both sides describe the same power series, one indexed by the exponent $k$ and the other by the triangular index $n$. This reindexing is used in the proof of Jacobi's identity (Chapter 19).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19_JacobiTripleSignChar.lean#L156-L199

import Definitions.Def_QseriesFormalization_DefCoreQSeries
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

theorem QseriesFormalization.PartIV.Ch19.tsum_jacobiTripleSign_eq_jacobi_series (q : ℂ) :
    ∑' k : ℕ, ((jacobiTripleSign k : ℤ) : ℂ) * q ^ k =
      ∑' n : ℕ, ((-1) ^ n * (2 * (n : ℂ) + 1) * q ^ (n * (n + 1) / 2)) := by sorry
