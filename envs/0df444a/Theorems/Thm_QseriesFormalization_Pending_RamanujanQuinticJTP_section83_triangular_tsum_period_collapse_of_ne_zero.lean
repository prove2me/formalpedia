-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_RamanujanQuinticJTP_section83_triangular_tsum_period_collapse_of_ne_zero
-- name    : QseriesFormalization.Pending.RamanujanQuinticJTP.section83_triangular_tsum_period_collapse_of_ne_zero
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T14:47:11.857651+00:00
-- url     : https://prove2.me/theorems/a8b86c5b-3a32-4b57-a5b5-2cc0995bb8fe
-- title:
--   Collapsing $\sum_n(-z)^nq^{n(n+1)/2}$ for a fifth root of unity $z$
-- statement:
--   Let $z,q\in\mathbb{C}$ with $z^5=1$, $z\ne0$, $0<|q|<1$. Then
--   $$\sum_{n\in\mathbb{Z}}(-z)^{n}q^{n(n+1)/2}=(1-z^{4})\sum_{k\in\mathbb{Z}}(-1)^kq^{5k(5k-1)/2}+(z^{3}-z)\,q\sum_{k\in\mathbb{Z}}(-1)^kq^{5k(5k-3)/2}.$$
--   The bilateral triangular series splits according to $n\bmod5$, using $z^5=1$, into the two mod-5 theta series evaluated at $q^5$. This is a step in Hirschhorn's section 8.3 argument.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/RamanujanQuinticJTP.lean#L1211-L1337

import Definitions.Def_QseriesFormalization_DefQuintic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith

namespace QseriesFormalization.Pending.Ch16MBIProof end QseriesFormalization.Pending.Ch16MBIProof

/-!
# Ramanujan quintic: JTP-at-a-fifth-root scaffolding

This file keeps the `a = eta` bookkeeping for Hirschhorn §8.3 separate from
the older finite product/cyclotomic infrastructure in `RamanujanQuintic`.

The main convention issue is that `RamanujanQuintic.quinticPeriodAlpha/Beta`
are the Gaussian periods

* `ζ + ζ^4`, `ζ^2 + ζ^3`, with sum `-1`;

whereas Hirschhorn §8.3 writes the golden-ratio pair with sum `1`.  The
definitions below expose the book's pair as the negatives of the appropriate
Gaussian periods.
-/

open QseriesFormalization
open QseriesFormalization.Pending
open QseriesFormalization.Pending.RamanujanQuinticJTP

open Finset
open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.RamanujanQuintic
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.Ch16MBIProof

/-! ## The §8.3 period convention -/

/-! ## Local factors for the `a = η²` specialization -/

/-! ## Book-period form of the §8.3 quadratic factors -/

/-! ## The fifth-power algebra used after the §8.3 factor identities -/

/-! ## Names for the two `A,B` series in Hirschhorn §8.3 -/

/-! ## Free-constant Euler factors for the §8.3 JTP product side -/

/-! ### Analytic product attached to the free-constant formal product -/

/-! ### Bilateral triangular terms for the fifth-root period collapse -/

theorem QseriesFormalization.Pending.RamanujanQuinticJTP.section83_triangular_tsum_period_collapse_of_ne_zero
    {z q : ℂ} (hz5 : z ^ 5 = 1) (hz : z ≠ 0)
    (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    (∑' n : ℤ, section83TriangularTerm z q n) =
      (1 - z ^ 4) * pentagonal023Analytic (q ^ 5) +
        (z ^ 3 - z) * q * pentagonal014Analytic (q ^ 5) := by sorry
