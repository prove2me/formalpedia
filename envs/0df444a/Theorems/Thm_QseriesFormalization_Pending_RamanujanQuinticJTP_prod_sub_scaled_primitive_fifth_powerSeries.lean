-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_RamanujanQuinticJTP_prod_sub_scaled_primitive_fifth_powerSeries
-- name    : QseriesFormalization.Pending.RamanujanQuinticJTP.prod_sub_scaled_primitive_fifth_powerSeries
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:44:45.869799+00:00
-- url     : https://prove2.me/theorems/11d10d27-3274-4cac-987e-194bc6290182
-- title:
--   Product over the five fifth-root multiples: $\prod_j(A-\mu^jcB)=A^5-c^5B^5$
-- statement:
--   Let $R$ be an integral domain, $\mu\in R$ a primitive $5$th root of unity, $c\in R$, and $A,B\in R[[X]]$. Then $$\prod_{j=0}^{4}\big(A-\mu^jc\,B\big)=A^5-c^5B^5,$$ where $c$ and $\mu^jc$ act as constants. Algebraic input to the quintic argument.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/RamanujanQuinticJTP.lean#L310-L328

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

theorem QseriesFormalization.Pending.RamanujanQuinticJTP.prod_sub_scaled_primitive_fifth_powerSeries {R : Type*}
    [CommRing R] [IsDomain R] {μ c : R} (A B : R⟦X⟧)
    (hμ : IsPrimitiveRoot μ 5) :
    ∏ j : Fin 5, (A - PowerSeries.C (μ ^ (j : ℕ) * c) * B) =
      A ^ 5 - PowerSeries.C (c ^ 5) * B ^ 5 := by sorry
