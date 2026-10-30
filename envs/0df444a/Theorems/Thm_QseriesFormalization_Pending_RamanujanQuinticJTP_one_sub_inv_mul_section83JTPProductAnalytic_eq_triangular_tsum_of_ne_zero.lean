-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_RamanujanQuinticJTP_one_sub_inv_mul_section83JTPProductAnalytic_eq_triangular_tsum_of_ne_zero
-- name    : QseriesFormalization.Pending.RamanujanQuinticJTP.one_sub_inv_mul_section83JTPProductAnalytic_eq_triangular_tsum_of_ne_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:43:55.650131+00:00
-- url     : https://prove2.me/theorems/10db315b-3d0c-462a-a3e2-39ac00fb5596
-- title:
--   Shifted Jacobi triple product: $(1-z^{-1})(q,zq,z^{-1}q;q)_\infty=\sum_{n\in\mathbb{Z}}(-z)^nq^{n(n+1)/2}$
-- statement:
--   For complex $z,q$ with $z\ne0$, $0<|q|<1$,
--   $$(1-z^{-1})\,(q;q)_\infty(zq;q)_\infty(z^{-1}q;q)_\infty=\sum_{n\in\mathbb{Z}}(-z)^{n}q^{n(n+1)/2}.$$
--   This is the Jacobi triple product in the shifted convention (triangular exponents) obtained from the Chapter 2 identity, used in Hirschhorn's section 8.3 derivation of Ramanujan's quintic identities.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/RamanujanQuinticJTP.lean#L758-L775

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

theorem QseriesFormalization.Pending.RamanujanQuinticJTP.one_sub_inv_mul_section83JTPProductAnalytic_eq_triangular_tsum_of_ne_zero
    (z q : ℂ) (hz : z ≠ 0) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    (1 - z⁻¹) * section83JTPProductAnalytic z q =
      ∑' n : ℤ, (-z : ℂ) ^ n * q ^ (n * (n + 1) / 2) := by sorry
