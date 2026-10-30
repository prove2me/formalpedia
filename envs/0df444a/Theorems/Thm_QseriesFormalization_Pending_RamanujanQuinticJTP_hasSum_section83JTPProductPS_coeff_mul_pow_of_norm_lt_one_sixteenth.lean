-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_RamanujanQuinticJTP_hasSum_section83JTPProductPS_coeff_mul_pow_of_norm_lt_one_sixteenth
-- name    : QseriesFormalization.Pending.RamanujanQuinticJTP.hasSum_section83JTPProductPS_coeff_mul_pow_of_norm_lt_one_sixteenth
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:41:41.225436+00:00
-- url     : https://prove2.me/theorems/4313951f-5abb-49d2-9fa8-feec878bd0d6
-- title:
--   Evaluating the formal product $(q,zq,z^{-1}q;q)_\infty$ at small $q$
-- statement:
--   Let $z\in\mathbb{C}$ with $|z|\le1$ and $|z^{-1}|\le1$ (equivalently, $z=0$ or $|z|=1$, using Lean’s totalized inverse $0^{-1}=0$), and let $q\in\mathbb{C}$ with $|q|<1/16$. The series $\sum_kc_kq^k$ built from the coefficients $c_k$ of the formal product $(q;q)_\infty(zq;q)_\infty(z^{-1}q;q)_\infty\in\mathbb{C}[[X]]$ converges to the analytic product $\prod_{n\ge1}(1-q^n)(1-zq^n)(1-z^{-1}q^n)$. This is the formal-to-analytic bridge for the quintic identity argument.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/RamanujanQuinticJTP.lean#L1428-L1477

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

theorem QseriesFormalization.Pending.RamanujanQuinticJTP.hasSum_section83JTPProductPS_coeff_mul_pow_of_norm_lt_one_sixteenth
    (z q : ℂ) (hz : ‖z‖ ≤ 1) (hzinv : ‖z⁻¹‖ ≤ 1)
    (hq : ‖q‖ < (1 / 16 : ℝ)) :
    HasSum (fun k : ℕ => (section83JTPProductPS z).coeff k * q ^ k)
      (section83JTPProductAnalytic z q) := by sorry
