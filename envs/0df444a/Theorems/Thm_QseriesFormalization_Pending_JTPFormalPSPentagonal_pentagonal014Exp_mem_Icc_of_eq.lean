-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSPentagonal_pentagonal014Exp_mem_Icc_of_eq
-- name    : QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal014Exp_mem_Icc_of_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:35:42.564666+00:00
-- url     : https://prove2.me/theorems/2893125c-4964-4825-a299-5db1c3a5a7da
-- title:
--   If $(5k^2-3k)/2=n$ then $|k|\le n+1$
-- statement:
--   Let $k$ be an integer and $n$ a natural number with $\lfloor(5k^2-3k)/2\rfloor=n$. Then $k\in[-(n+1),\,n+1]$. This bounds the indices contributing to a given coefficient of the theta series $\sum_k(-1)^kX^{(5k^2-3k)/2}$.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean#L229-L251

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

theorem QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal014Exp_mem_Icc_of_eq {k : ℤ} {n : ℕ} (h : pentagonal014Exp k = n) :
    k ∈ Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ) := by sorry
