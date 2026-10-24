-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSPentagonal_hasSum_pentagonalProduct014PS_coeff_mul_pow_of_norm_lt_one_sixteenth
-- name    : QseriesFormalization.Pending.JTPFormalPSPentagonal.hasSum_pentagonalProduct014PS_coeff_mul_pow_of_norm_lt_one_sixteenth
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T14:32:38.106968+00:00
-- url     : https://prove2.me/theorems/6ba1f91c-5650-40e6-8184-58ba766203df
-- title:
--   Evaluating the formal product $(q,q^4,q^5;q^5)_\infty$ at small $q$ gives the analytic product
-- statement:
--   For $q\in\mathbb{C}$ with $|q|<1/16$, the series $\sum_kc_kq^k$ built from the coefficients $c_k$ of the formal product $(q;q^5)_\infty(q^4;q^5)_\infty(q^5;q^5)_\infty\in\mathbb{C}[[X]]$ converges to the analytic product $\prod_{n\ge0}(1-q^{5n+5})(1-q^{5n+4})(1-q^{5n+1})$. The bound $|q|<1/16$ comes from the coefficient estimate $8^N$. This is the formal-to-analytic bridge for the first mod-5 triple product.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean#L1198-L1248

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

theorem QseriesFormalization.Pending.JTPFormalPSPentagonal.hasSum_pentagonalProduct014PS_coeff_mul_pow_of_norm_lt_one_sixteenth
    (q : ℂ) (hq : ‖q‖ < (1 / 16 : ℝ)) :
    HasSum (fun k : ℕ => (pentagonalProduct014PS ℂ).coeff k * q ^ k)
      (pentagonal014ProductAnalytic q) := by sorry
