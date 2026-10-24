-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSPentagonal_pentagonal023Exp_mem_Icc_of_eq
-- name    : QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal023Exp_mem_Icc_of_eq
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T14:36:16.223182+00:00
-- url     : https://prove2.me/theorems/c3a72c40-55c4-456d-b479-d6bf1403cfa8
-- title:
--   If $(5k^2-k)/2=n$ then $|k|\le n+1$
-- statement:
--   Let $k$ be an integer and $n$ a natural number with $\lfloor(5k^2-k)/2\rfloor=n$ (natural-number exponent). Then $k$ lies in the interval $[-(n+1),\,n+1]$. This bounds the indices contributing to a given coefficient of the theta series $\sum_k(-1)^kX^{(5k^2-k)/2}$ and is a technical lemma in the formal-series Jacobi triple product development.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean#L253-L275

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

theorem QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal023Exp_mem_Icc_of_eq {k : ℤ} {n : ℕ} (h : pentagonal023Exp k = n) :
    k ∈ Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ) := by sorry
