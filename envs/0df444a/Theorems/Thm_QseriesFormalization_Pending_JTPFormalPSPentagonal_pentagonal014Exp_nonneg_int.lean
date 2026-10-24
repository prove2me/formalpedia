-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSPentagonal_pentagonal014Exp_nonneg_int
-- name    : QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal014Exp_nonneg_int
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T14:35:36.465059+00:00
-- url     : https://prove2.me/theorems/5811cf9c-fc8d-43a3-9a71-a968a442f419
-- title:
--   The exponent $k(5k-3)/2$ is nonnegative for every integer $k$
-- statement:
--   For every integer $k$, $0\le k(5k-3)/2$ (integer division). Hence the exponent $(5k^2-3k)/2$ of the theta series $\sum_k(-1)^kX^{(5k^2-3k)/2}$ is a natural number. This is a technical lemma in the formal-series Jacobi triple product development.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean#L162-L174

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

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology

/-! ## Formal AP products -/

/-! ## Formal bilateral series coefficients -/

/-! ## Bilateral theta analytic-to-formal bridge -/

theorem QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal014Exp_nonneg_int (k : ℤ) :
    0 ≤ k * (5 * k - 3) / 2 := by sorry
