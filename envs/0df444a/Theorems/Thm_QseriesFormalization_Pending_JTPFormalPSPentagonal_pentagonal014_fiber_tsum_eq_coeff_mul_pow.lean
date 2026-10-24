-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSPentagonal_pentagonal014_fiber_tsum_eq_coeff_mul_pow
-- name    : QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal014_fiber_tsum_eq_coeff_mul_pow
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T14:36:23.815389+00:00
-- url     : https://prove2.me/theorems/7e536ce4-3c03-4e61-9ef8-57bbdaacd55a
-- title:
--   Grouping the $(5k^2-3k)/2$ theta series by exponent
-- statement:
--   For $q\in\mathbb{C}$ and $n\in\mathbb{N}$, the sum of the theta terms $(-1)^{|k|}q^{\lfloor(5k^2-3k)/2\rfloor}$ over all integers $k$ with $\lfloor(5k^2-3k)/2\rfloor=n$ equals $c_n\,q^n$, where $c_n$ is the coefficient of $X^n$ in the formal series $\sum_k(-1)^kX^{(5k^2-3k)/2}$. This regroups the analytic theta series by powers of $q$.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean#L403-L423

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

theorem QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal014_fiber_tsum_eq_coeff_mul_pow (q : ℂ) (n : ℕ) :
    (∑' k : ↑(pentagonal014Exp ⁻¹' ({n} : Set ℕ)), pentagonal014ThetaTerm q k) =
      pentagonal014Coeff ℂ n * q ^ n := by sorry
