-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSPentagonal_pentagonalProduct014PS_eq_tprod
-- name    : QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonalProduct014PS_eq_tprod
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:37:46.224155+00:00
-- url     : https://prove2.me/theorems/489436d6-8d08-4410-acf0-5673ac50623c
-- title:
--   Triple product $(q,q^4,q^5;q^5)_\infty$ as an infinite product of triple factors
-- statement:
--   Let $R$ be a commutative Hausdorff topological ring. In $R[[X]]$ (with the product topology), $$(q,q^4,q^5;q^5)_\infty=\prod_{n\ge0}(1-X^{1+5n})(1-X^{4+5n})(1-X^{5+5n}),$$ i.e. the product of the three arithmetic-progression products equals the single infinite product (in the sense of Lean `tprod`) over $n$ of the per-$n$ triple factors. A regrouping lemma of the mod-5 Jacobi triple product setting.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean#L104-L108

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

theorem QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonalProduct014PS_eq_tprod
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    pentagonalProduct014PS R = ∏' n : ℕ, pentagonalTripleFactor014PS R n := by sorry
