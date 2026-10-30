-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch15WronskianIndependent_wronskianCore_add_conj_of_norm_odd
-- name    : QseriesFormalization.Pending.Ch15WronskianIndependent.wronskianCore_add_conj_of_norm_odd
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T11:20:34.709703+00:00
-- url     : https://prove2.me/theorems/889cfba9-e18a-40c0-973a-6ca946dace3d
-- title:
--   Conjugate pair sum of the Wronskian core: $w(a,b)+w(a,-b)=-2(a^2-b^2)$
-- statement:
--   For integers $a,b$ with $a^2+b^2$ odd, the Wronskian core $w(a,b)=\big((-a-3b)^2-(3a-b)^2\big)/8$ (exact division) satisfies $$w(a,b)+w(a,-b)=-2(a^2-b^2).$$ Chapter 15.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 15. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean#L2568-L2590

import Definitions.Def_QseriesFormalization_Pending_Chapter15_WronskianIndependent
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

namespace QseriesFormalization.Pending.Ch13RRCF end QseriesFormalization.Pending.Ch13RRCF
namespace QseriesFormalization.Pending.Ch16MBIProof end QseriesFormalization.Pending.Ch16MBIProof
namespace QseriesFormalization.Pending.JacobiCubeAnalyticToFormal end QseriesFormalization.Pending.JacobiCubeAnalyticToFormal

/-!
# Chapter 15 — independent Wronskian coefficient reduction

This file deliberately avoids importing `Chapter15_R_ODE` and any theorem
depending on `chan_theorem_11_7`.  The remaining open mathematical point is the
all-degree finite double-sum identity between the pentagonal Wronskian
coefficients and the Jacobi-cube Cauchy-square coefficients.
-/

open QseriesFormalization
open QseriesFormalization.Pending
open QseriesFormalization.Pending.Ch15WronskianIndependent

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

theorem QseriesFormalization.Pending.Ch15WronskianIndependent.wronskianCore_add_conj_of_norm_odd {a b : ℤ}
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1) :
    wronskianCore a b + wronskianCore a (-b) =
      -2 * (a ^ 2 - b ^ 2) := by sorry
