-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_RamanujanQuinticJTP_hasSum_section83A_coeff_mul_pow
-- name    : QseriesFormalization.Pending.RamanujanQuinticJTP.hasSum_section83A_coeff_mul_pow
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:41:08.983959+00:00
-- url     : https://prove2.me/theorems/fd4580e2-2f84-48d8-a57b-7f18a703991c
-- title:
--   Evaluating the formal series $A$ at $q$ gives the theta series $\sum_k(-1)^kq^{5(5k^2-k)/2}$
-- statement:
--   For $q\in\mathbb{C}$ with $|q|<1$, the power series $\sum_nc_nq^n$ built from the coefficients of $A=\sum_{k}(-1)^kX^{5(5k^2-k)/2}\in\mathbb{C}[[X]]$ (the series `section83A`, i.e. $\sum_k(-1)^kX^{(5k^2-k)/2}$ with $X\mapsto X^5$) converges to the analytic theta series $\sum_{k\in\mathbb{Z}}(-1)^kq^{5(5k^2-k)/2}$. This identifies the formal series with its analytic evaluation.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/RamanujanQuinticJTP.lean#L1710-L1733

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

theorem QseriesFormalization.Pending.RamanujanQuinticJTP.hasSum_section83A_coeff_mul_pow (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (section83A ℂ).coeff n * q ^ n)
      (pentagonal023Analytic (q ^ 5)) := by sorry
