-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSPentagonal_norm_coeff_partial_pentagonalTripleFactor023PS_complex_le
-- name    : QseriesFormalization.Pending.JTPFormalPSPentagonal.norm_coeff_partial_pentagonalTripleFactor023PS_complex_le
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T14:34:39.370982+00:00
-- url     : https://prove2.me/theorems/94f30eb1-9f25-49a3-96aa-e00f3bc9a056
-- title:
--   Coefficients of finite partial products are bounded by $8^N$
-- statement:
--   For all natural numbers $N,k$, the $k$-th coefficient of the finite product $\prod_{n=0}^{N-1}(1-X^{2+5n})(1-X^{3+5n})(1-X^{5+5n})\in\mathbb{C}[[X]]$ has norm at most $8^N$. This crude exponential bound leads to convergence of the product series for small $|q|$ (see the next lemmas).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean#L1004-L1025

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Formal power-series shells for the mod-5 JTP pentagonal specialisations

This pending file isolates the formal objects for Hirschhorn's two
mod-5 Jacobi-triple-product specialisations.  The full analytic-to-formal
coefficient bridge is not asserted here; all declarations below are fully
proved.
-/

open QseriesFormalization
open QseriesFormalization.Pending
open QseriesFormalization.Pending.JTPFormalPSPentagonal

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology

/-! ## Formal AP products -/

/-! ## Formal bilateral series coefficients -/

/-! ## Bilateral theta analytic-to-formal bridge -/

/-! ## Analytic identities already closed in Chapter 4, in target exponent orientation -/

/-! ## Product-side analytic functions, with the puncture at `q = 0` filled -/

/-! ## Final uniqueness step, conditional on the product-coefficient Taylor bridge -/

/-! ### Product-coefficient finite partial bridges -/

theorem QseriesFormalization.Pending.JTPFormalPSPentagonal.norm_coeff_partial_pentagonalTripleFactor023PS_complex_le
    (N k : ℕ) :
    ‖(∏ n ∈ Finset.range N, pentagonalTripleFactor023PS ℂ n).coeff k‖ ≤
      (8 : ℝ) ^ N := by sorry
