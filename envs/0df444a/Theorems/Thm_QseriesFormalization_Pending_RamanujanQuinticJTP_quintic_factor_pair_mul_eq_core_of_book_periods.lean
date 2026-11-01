-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_RamanujanQuinticJTP_quintic_factor_pair_mul_eq_core_of_book_periods
-- name    : QseriesFormalization.Pending.RamanujanQuinticJTP.quintic_factor_pair_mul_eq_core_of_book_periods
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:45:26.657909+00:00
-- url     : https://prove2.me/theorems/cd3c4811-745e-4526-b7a6-d51766d3fa4d
-- title:
--   Factor pair in terms of the book periods: $(G^5-\beta^5XH^5)(G^5-\alpha^5XH^5)=$ product core
-- statement:
--   Let $R$ be an integral domain, $\zeta\in R$ a primitive $5$th root of unity, $\alpha=-(\zeta^2+\zeta^3)$, $\beta=-(\zeta+\zeta^4)$ (Hirschhorn's golden-ratio conjugates), and $G,H\in R[[X]]$. Then $$\big(G^5-\beta^5XH^5\big)\big(G^5-\alpha^5XH^5\big)=G^{10}-11XH^5G^5-X^2H^{10}.$$ Chapter-level algebra for the mod-5 quintic argument.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/RamanujanQuinticJTP.lean#L330-L341

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

theorem QseriesFormalization.Pending.RamanujanQuinticJTP.quintic_factor_pair_mul_eq_core_of_book_periods {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (H G : R⟦X⟧) :
    (G ^ 5 - PowerSeries.C ((bookBeta ζ) ^ 5) *
          PowerSeries.X * H ^ 5) *
        (G ^ 5 - PowerSeries.C ((bookAlpha ζ) ^ 5) *
          PowerSeries.X * H ^ 5) =
      quinticProductCore R H G := by sorry
