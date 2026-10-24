-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_RamanujanQuinticJTP_hasSum_coeff_mul_constQFactorPS_complex
-- name    : QseriesFormalization.Pending.RamanujanQuinticJTP.hasSum_coeff_mul_constQFactorPS_complex
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T14:40:57.143624+00:00
-- url     : https://prove2.me/theorems/585bb360-15ab-42e6-9011-3ac82ca088a0
-- title:
--   Evaluating a power series times $1-cX^{N+1}$
-- statement:
--   Let $P\in\mathbb{C}[[X]]$ and $q,p,c\in\mathbb{C}$, $N\in\mathbb{N}$, such that $\sum_kP_kq^k$ converges to $p$. Then $\sum_k(P\cdot(1-cX^{N+1}))_kq^k$ converges to $p\,(1-cq^{N+1})$. That is, evaluation at $q$ is multiplicative for such a factor. This is used in the formal-to-analytic comparison of the products $(cq;q)_\infty$.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/RamanujanQuinticJTP.lean#L1339-L1389

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

theorem QseriesFormalization.Pending.RamanujanQuinticJTP.hasSum_coeff_mul_constQFactorPS_complex
    (P : ℂ⟦X⟧) (q p c : ℂ) (N : ℕ)
    (hP : HasSum (fun k : ℕ => P.coeff k * q ^ k) p) :
    HasSum (fun k : ℕ => (P * constQFactorPS c N).coeff k * q ^ k)
      (p * (1 - c * q ^ (N + 1))) := by sorry
