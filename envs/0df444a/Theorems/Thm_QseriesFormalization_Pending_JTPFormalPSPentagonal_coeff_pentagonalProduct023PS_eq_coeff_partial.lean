-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSPentagonal_coeff_pentagonalProduct023PS_eq_coeff_partial
-- name    : QseriesFormalization.Pending.JTPFormalPSPentagonal.coeff_pentagonalProduct023PS_eq_coeff_partial
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T14:31:58.330008+00:00
-- url     : https://prove2.me/theorems/88b1b858-ddeb-446e-8771-b39f2449b572
-- title:
--   Coefficients of $(q^2,q^3,q^5;q^5)_\infty$ are those of a finite partial product
-- statement:
--   Let $R$ be a commutative Hausdorff topological ring and $k\in\mathbb{N}$. The $k$-th coefficient of the formal infinite product $(q^2;q^5)_\infty(q^3;q^5)_\infty(q^5;q^5)_\infty$ in $R[[X]]$ equals the $k$-th coefficient of the finite product $\prod_{n=0}^{k}(1-X^{2+5n})(1-X^{3+5n})(1-X^{5+5n})$. This reduces coefficients of the infinite product to finite computations.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean#L867-L890

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

theorem QseriesFormalization.Pending.JTPFormalPSPentagonal.coeff_pentagonalProduct023PS_eq_coeff_partial
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (k : ℕ) :
    (pentagonalProduct023PS R).coeff k =
      (∏ n ∈ Finset.range (k + 1), pentagonalTripleFactor023PS R n).coeff k := by sorry
