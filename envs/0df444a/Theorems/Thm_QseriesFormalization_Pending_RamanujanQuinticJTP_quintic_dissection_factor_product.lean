-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_RamanujanQuinticJTP_quintic_dissection_factor_product
-- name    : QseriesFormalization.Pending.RamanujanQuinticJTP.quintic_dissection_factor_product
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T14:45:11.703749+00:00
-- url     : https://prove2.me/theorems/40fb0f3b-1374-4360-a9fc-7f755dae30eb
-- title:
--   Norm of a $5$-fold cyclic product: $\prod_j(A+z^jB+z^{2j}D)=A^5+11B^5+D^5$ when $AD=-B^2$
-- statement:
--   Let $S$ be a commutative ring and $z\in S$ with $z^5=1$ and $z^4=-(1+z+z^2+z^3)$ (so $1+z+z^2+z^3+z^4=0$). For $A,B,D\in S$ with $AD=-B^2$, $$\prod_{j=0}^{4}\big(A+z^jB+z^{2j}D\big)=A^5+11B^5+D^5.$$ This is the algebraic identity that rationalizes the mod-5 dissection of Euler's product.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/RamanujanQuinticJTP.lean#L2262-L2296

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

namespace QseriesFormalization.PartIV.Ch19 end QseriesFormalization.PartIV.Ch19
namespace QseriesFormalization.Pending.Ch16MBIProof end QseriesFormalization.Pending.Ch16MBIProof
namespace QseriesFormalization.Pending.JTPFormalPSPentagonal end QseriesFormalization.Pending.JTPFormalPSPentagonal
namespace QseriesFormalization.Pending.RamanujanQuintic end QseriesFormalization.Pending.RamanujanQuintic

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

/-! ## Infinite fifth-root product collapse -/

/-! ## Identification with the Chapter 16 denominator core -/

theorem QseriesFormalization.Pending.RamanujanQuinticJTP.quintic_dissection_factor_product {S : Type*} [CommRing S]
    {z : S} (hz4 : z^4 = -(1 + z + z^2 + z^3)) (hz5 : z^5 = 1)
    (A B D : S) (hAD : A * D = -B^2) :
    ∏ j : Fin 5, (A + z ^ (j : ℕ) * B + z ^ (2 * (j : ℕ)) * D) =
      A^5 + 11 * B^5 + D^5 := by sorry
