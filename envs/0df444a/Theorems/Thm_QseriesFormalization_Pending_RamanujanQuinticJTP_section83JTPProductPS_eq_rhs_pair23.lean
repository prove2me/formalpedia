-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_RamanujanQuinticJTP_section83JTPProductPS_eq_rhs_pair23
-- name    : QseriesFormalization.Pending.RamanujanQuinticJTP.section83JTPProductPS_eq_rhs_pair23
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T14:46:32.754718+00:00
-- url     : https://prove2.me/theorems/b99e0e30-1353-4db9-a072-a0a18f54cd54
-- title:
--   Hirschhorn's identity for $\zeta^2$: $(q,\zeta^2q,\zeta^{-2}q;q)_\infty=A+(\zeta+\zeta^4)\,qB$
-- statement:
--   Let $\zeta\in\mathbb{C}$ be a primitive fifth root of unity. In $\mathbb{C}[[X]]$,
--   $$(q;q)_\infty(\zeta^2q;q)_\infty(\zeta^{-2}q;q)_\infty=A+(\zeta+\zeta^4)\,X\,B,$$
--   where $A=\sum_{k\in\mathbb{Z}}(-1)^kX^{5(5k^2-k)/2}$ and $B=\sum_{k\in\mathbb{Z}}(-1)^kX^{5(5k^2-3k)/2}$ are the two mod-5 theta series with $X$ replaced by $X^5$. This is the companion identity (8.3.1) for the other conjugate pair, obtained by applying the previous identity to the primitive root $\zeta^2$.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/RamanujanQuinticJTP.lean#L2002-L2006

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

theorem QseriesFormalization.Pending.RamanujanQuinticJTP.section83JTPProductPS_eq_rhs_pair23
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    section83JTPProductPS (ζ ^ 2) = section83_rhs_pair23 ζ := by sorry
