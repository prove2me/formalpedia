-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_RamanujanQuinticJTP_E5DenominatorCoreRat_mul_expand_twentyfive_qPochInfPS
-- name    : QseriesFormalization.Pending.RamanujanQuinticJTP.E5DenominatorCoreRat_mul_expand_twentyfive_qPochInfPS
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:39:32.285986+00:00
-- url     : https://prove2.me/theorems/cc1f68a5-6f71-4900-9ba7-c65665f69e15
-- title:
--   $(E_0^5+11E_1^5+E_2^5)\cdot E(q^{25})=E(q^5)^6$ in $\mathbb{Q}[[X]]$
-- statement:
--   Let $E(q)=(q;q)_\infty\in\mathbb{Q}[[X]]$ and $E_r$ its section of exponents $\equiv r\pmod 5$. Then $$\big(E_0^5+11E_1^5+E_2^5\big)\cdot E(q^{25})=E(q^5)^6.$$ This closes the eta-product identity for the mod-5 denominator core; used in Chapter 13 for Eq. (12.37)-type arguments.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/RamanujanQuinticJTP.lean#L2369-L2387

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

open QseriesFormalization
open QseriesFormalization.Pending

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

theorem QseriesFormalization.Pending.RamanujanQuinticJTP.E5DenominatorCoreRat_mul_expand_twentyfive_qPochInfPS :
    E5DenominatorCoreRat *
        PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) =
      (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 := by sorry
