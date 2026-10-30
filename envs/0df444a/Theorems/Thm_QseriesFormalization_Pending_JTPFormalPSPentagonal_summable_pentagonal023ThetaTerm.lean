-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSPentagonal_summable_pentagonal023ThetaTerm
-- name    : QseriesFormalization.Pending.JTPFormalPSPentagonal.summable_pentagonal023ThetaTerm
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:38:27.682974+00:00
-- url     : https://prove2.me/theorems/88be70bd-ffad-4d2c-91ce-d1f0ff71fe14
-- title:
--   Summability of $\sum_{k\in\mathbb{Z}}(-1)^kq^{(5k^2-k)/2}$ for $|q|<1$
-- statement:
--   For $q\in\mathbb{C}$ with $|q|<1$, the family $k\mapsto(-1)^{|k|}q^{\lfloor(5k^2-k)/2\rfloor}$ (taking the natural-number exponent) is summable over $k\in\mathbb{Z}$. This is the convergence of the theta series on the series side of a mod-5 Jacobi triple product identity, in the formal-series development.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean#L371-L401

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

theorem QseriesFormalization.Pending.JTPFormalPSPentagonal.summable_pentagonal023ThetaTerm (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun k : ℤ => pentagonal023ThetaTerm q k := by sorry
