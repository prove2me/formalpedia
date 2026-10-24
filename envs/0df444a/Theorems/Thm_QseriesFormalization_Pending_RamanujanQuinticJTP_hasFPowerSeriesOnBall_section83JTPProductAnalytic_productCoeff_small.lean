-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_RamanujanQuinticJTP_hasFPowerSeriesOnBall_section83JTPProductAnalytic_productCoeff_small
-- name    : QseriesFormalization.Pending.RamanujanQuinticJTP.hasFPowerSeriesOnBall_section83JTPProductAnalytic_productCoeff_small
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T14:40:01.442781+00:00
-- url     : https://prove2.me/theorems/0f27156a-8e14-49f5-b0bb-5adce22ffb56
-- title:
--   The analytic product $(q,zq,z^{-1}q;q)_\infty$ has the formal product's coefficients as its Taylor series near $0$
-- statement:
--   Let $z\in\mathbb{C}$ with $|z|\le1$ and $|z^{-1}|\le1$ (equivalently, $z=0$ or $|z|=1$, using Lean’s totalized inverse $0^{-1}=0$). The analytic function $q\mapsto\prod_{n\ge1}(1-q^n)(1-zq^n)(1-z^{-1}q^n)$ has a power series expansion at $0$, valid on the ball of radius $1/16$, whose coefficients are those of the formal product $(q;q)_\infty(zq;q)_\infty(z^{-1}q;q)_\infty$. This lets one compare formal power series identities with analytic ones by uniqueness of Taylor expansions.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/RamanujanQuinticJTP.lean#L1506 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

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

theorem QseriesFormalization.Pending.RamanujanQuinticJTP.hasFPowerSeriesOnBall_section83JTPProductAnalytic_productCoeff_small
    (z : ℂ) (hz : ‖z‖ ≤ 1) (hzinv : ‖z⁻¹‖ ≤ 1) :
    HasFPowerSeriesOnBall (section83JTPProductAnalytic z)
      (section83JTPProductCoeffFMLS z) 0 ((1 / 16 : NNReal) : ENNReal) := by sorry
