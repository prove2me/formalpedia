-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch15WronskianIndependent_wronskianSelector_exists_int
-- name    : QseriesFormalization.Pending.Ch15WronskianIndependent.wronskianSelector_exists_int
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T11:20:51.851986+00:00
-- url     : https://prove2.me/theorems/15a9dd57-39ce-48d2-bea2-af36057472d6
-- title:
--   If $5\nmid a^2+b^2$, one of four linear forms in $(a,b)$ is $\equiv2\pmod5$
-- statement:
--   For integers $a,b$ with $a^2+b^2\not\equiv0\pmod 5$, at least one of $-a-3b$, $-3a+b$, $a+3b$, $3a-b$ is congruent to $2$ modulo $5$. This selects the unit rotation used in the Wronskian weight. Chapter 15.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 15. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean#L2474 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

namespace QseriesFormalization.PartIV.Ch19 end QseriesFormalization.PartIV.Ch19
namespace QseriesFormalization.Pending.Ch10TenthOrder end QseriesFormalization.Pending.Ch10TenthOrder
namespace QseriesFormalization.Pending.Ch13RRCF end QseriesFormalization.Pending.Ch13RRCF
namespace QseriesFormalization.Pending.Ch15FormalDeriv end QseriesFormalization.Pending.Ch15FormalDeriv
namespace QseriesFormalization.Pending.Ch16MBIProof end QseriesFormalization.Pending.Ch16MBIProof
namespace QseriesFormalization.Pending.JTPFormalPSPentagonal end QseriesFormalization.Pending.JTPFormalPSPentagonal
namespace QseriesFormalization.Pending.JacobiCubeAnalyticToFormal end QseriesFormalization.Pending.JacobiCubeAnalyticToFormal

/-!
# Chapter 15 — independent Wronskian coefficient reduction

This file deliberately avoids importing `Chapter15_R_ODE` and any theorem
depending on `chan_theorem_11_7`.  The remaining open mathematical point is the
all-degree finite double-sum identity between the pentagonal Wronskian
coefficients and the Jacobi-cube Cauchy-square coefficients.
-/

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Ch15FormalDeriv
open QseriesFormalization.Pending.Ch16MBIProof
open QseriesFormalization.Pending.Ch13RRCF
open QseriesFormalization.Pending.Ch10TenthOrder
open QseriesFormalization.Pending.JacobiCubeAnalyticToFormal
open QseriesFormalization.Pending.JTPFormalPSPentagonal

/-! ## Quintuple-product logarithmic-derivative route scaffolding -/

/-! ### Executable coefficient model for the cleared logarithmic target -/

/-! ### Direct coefficient model for the eta-quotient side -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-! ### Prime-power local Eisenstein structure -/

/-! ### Theta-log recurrence form of the eta-quotient gap -/

/-! ## Gaussian-integer scaffolding for the 5-string proof -/

theorem QseriesFormalization.Pending.Ch15WronskianIndependent.wronskianSelector_exists_int (a b : ℤ)
    (h5 : (a ^ 2 + b ^ 2) % 5 ≠ 0) :
    (-a - 3 * b) % 5 = 2 ∨ (-3 * a + b) % 5 = 2 ∨
      (a + 3 * b) % 5 = 2 ∨ (3 * a - b) % 5 = 2 := by sorry
