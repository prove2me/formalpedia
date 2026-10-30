-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSPentagonal_multipliable_apFactorPS
-- name    : QseriesFormalization.Pending.JTPFormalPSPentagonal.multipliable_apFactorPS
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:33:15.950626+00:00
-- url     : https://prove2.me/theorems/37628745-3ca6-46f2-8e54-30323bdeeb9d
-- title:
--   Arithmetic-progression products $\prod_n(1-X^{r+mn})$ are multipliable for $m>0$
-- statement:
--   Let $R$ be a commutative ring with a topology, with $R[[X]]$ carrying the product topology, and let $r,m$ be natural numbers with $m>0$. The family of factors $n\mapsto1-X^{r+mn}$ is multipliable in $R[[X]]$, i.e. the formal infinite product $\prod_{n\ge0}(1-X^{r+mn})=(q^r;q^m)_\infty$ is well defined. This is a convergence fact in the formal-series treatment of the mod-5 Jacobi triple product products (pending development of Chapters 16-17).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean#L35-L51

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

theorem QseriesFormalization.Pending.JTPFormalPSPentagonal.multipliable_apFactorPS (R : Type*) [CommRing R] [TopologicalSpace R]
    (r m : ℕ) (hm : 0 < m) :
    Multipliable fun n : ℕ => apFactorPS R r m n := by sorry
