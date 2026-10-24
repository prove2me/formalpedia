-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_RamanujanQuinticJTP_norm_coeff_mul_section83JTPTripleFactorPS_complex_le
-- name    : QseriesFormalization.Pending.RamanujanQuinticJTP.norm_coeff_mul_section83JTPTripleFactorPS_complex_le
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T14:43:23.45135+00:00
-- url     : https://prove2.me/theorems/a2574309-2f53-4e7f-bf73-e31992178229
-- title:
--   Coefficient bound after multiplying by one triple factor $(1-X^{N+1})(1-zX^{N+1})(1-z^{-1}X^{N+1})$
-- statement:
--   Let $P\in\mathbb{C}[[X]]$ and $B\ge0$ with every coefficient of $P$ of norm at most $B$, and let $z\in\mathbb{C}$ with $|z|\le1$ and $|z^{-1}|\le1$ (equivalently, $z=0$ or $|z|=1$, using Lean’s totalized inverse $0^{-1}=0$). Then for all $k,N$, the $k$-th coefficient of $P\cdot(1-X^{N+1})(1-zX^{N+1})(1-z^{-1}X^{N+1})$ has norm at most $8B$.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/RamanujanQuinticJTP.lean#L527-L550

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

theorem QseriesFormalization.Pending.RamanujanQuinticJTP.norm_coeff_mul_section83JTPTripleFactorPS_complex_le
    (P : ℂ⟦X⟧) (B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ k : ℕ, ‖P.coeff k‖ ≤ B) (z : ℂ)
    (hz : ‖z‖ ≤ 1) (hzinv : ‖z⁻¹‖ ≤ 1) (k N : ℕ) :
    ‖(P * section83JTPTripleFactorPS z N).coeff k‖ ≤ 8 * B := by sorry
