-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_RamanujanQuinticJTP_section83JTPProductPS_eq_rhs_pair14_of_rhs_taylor
-- name    : QseriesFormalization.Pending.RamanujanQuinticJTP.section83JTPProductPS_eq_rhs_pair14_of_rhs_taylor
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:46:27.545401+00:00
-- url     : https://prove2.me/theorems/ca8a6d44-a497-4a6c-ac1b-32ae9e0a0e54
-- title:
--   Formal identity for $(\zeta q,\zeta^{-1}q,q;q)_\infty$, conditional on a Taylor-ball hypothesis
-- statement:
--   Let $\zeta\in\mathbb{C}$ be a primitive fifth root of unity. Assume that the series $A+(\zeta^2+\zeta^3)XB$ (the two-term right side, where $A=\sum_{k\in\mathbb{Z}}(-1)^kX^{5(5k^2-k)/2}$ and $B=\sum_{k\in\mathbb{Z}}(-1)^kX^{5(5k^2-3k)/2}$ are the two mod-5 theta series with $X$ replaced by $X^5$) is a power series expansion on the unit ball of the analytic product $(q,\zeta q,\zeta^{-1}q;q)_\infty$. Then, in $\mathbb{C}[[X]]$,
--   $$(q;q)_\infty(\zeta q;q)_\infty(\zeta^{-1}q;q)_\infty=A+(\zeta^2+\zeta^3)\,X\,B.$$
--   This is a conditional step, and the next statement removes the hypothesis.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/RamanujanQuinticJTP.lean#L1939-L1964

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

/-! ### Keystone-style transfer for the two §8.3 factors

The declarations below deliberately isolate the remaining analytic theorem:
the RHS period-collapse Taylor expansion must be proved for the same analytic
product.  Once that is available, `eq_formalMultilinearSeries` gives the formal
identity exactly as in `JTP_FormalPS_Pentagonal`.
-/

theorem QseriesFormalization.Pending.RamanujanQuinticJTP.section83JTPProductPS_eq_rhs_pair14_of_rhs_taylor
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (hrhs :
      HasFPowerSeriesOnBall (section83JTPProductAnalytic ζ)
        (section83RhsPair14FMLS ζ) 0 1) :
    section83JTPProductPS ζ = section83_rhs_pair14 ζ := by sorry
