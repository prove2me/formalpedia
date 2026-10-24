-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSPentagonal_negOnePowInt_complex_eq_zpow
-- name    : QseriesFormalization.Pending.JTPFormalPSPentagonal.negOnePowInt_complex_eq_zpow
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T14:33:24.940905+00:00
-- url     : https://prove2.me/theorems/3e08ea30-65e5-4667-b518-aee107f306b4
-- title:
--   The ring-generic sign $(-1)^{|k|}$ equals $(-1)^k$ in $\mathbb{C}$
-- statement:
--   For every integer $k$, the sign $(-1)^{|k|}$ (the Lean function `negOnePowInt`, defined with the absolute value of $k$ as a natural-number exponent) agrees over $\mathbb{C}$ with the integer power $(-1)^k$. This is a small compatibility lemma for the formal-series version of the Jacobi triple product.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean#L277-L289

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

theorem QseriesFormalization.Pending.JTPFormalPSPentagonal.negOnePowInt_complex_eq_zpow (k : ℤ) :
    negOnePowInt ℂ k = (-1 : ℂ) ^ k := by sorry
