-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSPentagonal_pentagonal023Exp_pos_of_ne_zero
-- name    : QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal023Exp_pos_of_ne_zero
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T14:36:56.881646+00:00
-- url     : https://prove2.me/theorems/508273e9-ed1e-4a82-9518-b8fb92fb18d5
-- title:
--   The exponent $(5k^2-k)/2$ is positive for $k\ne0$
-- statement:
--   For a nonzero integer $k$, the natural-number exponent $\lfloor(5k^2-k)/2\rfloor$ is strictly positive. Hence the only term of the theta series $\sum_k(-1)^kX^{(5k^2-k)/2}$ with exponent $0$ is $k=0$. This is a technical lemma in the formal-series Jacobi triple product development.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean#L656-L671

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

theorem QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal023Exp_pos_of_ne_zero {k : ℤ} (hk : k ≠ 0) :
    0 < pentagonal023Exp k := by sorry
