-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSPentagonal_hasSum_coeff_mul_apFactorPS_complex
-- name    : QseriesFormalization.Pending.JTPFormalPSPentagonal.hasSum_coeff_mul_apFactorPS_complex
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T14:32:21.901325+00:00
-- url     : https://prove2.me/theorems/57ba209b-ed4e-48fd-aa38-5258f284e1a6
-- title:
--   Multiplying a convergent power series by $1-X^{r+mN}$ preserves the evaluation limit
-- statement:
--   Let $P\in\mathbb{C}[[X]]$ and $q,p\in\mathbb{C}$ such that $\sum_kP_kq^k$ converges to $p$. For natural numbers $r,m,N$, the series $P\cdot(1-X^{r+mN})$ satisfies
--   $$\sum_{k}\big(P\,(1-X^{r+mN})\big)_kq^k=p\,(1-q^{r+mN}),$$
--   in the sense of convergent sums. That is, evaluation at $q$ is multiplicative for such a factor. This is used in the formal-to-analytic comparison of the mod-5 triple products.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean#L1061-L1102

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

theorem QseriesFormalization.Pending.JTPFormalPSPentagonal.hasSum_coeff_mul_apFactorPS_complex
    (P : ℂ⟦X⟧) (q p : ℂ) (r m N : ℕ)
    (hP : HasSum (fun k : ℕ => P.coeff k * q ^ k) p) :
    HasSum (fun k : ℕ => (P * apFactorPS ℂ r m N).coeff k * q ^ k)
      (p * (1 - q ^ (r + m * N))) := by sorry
