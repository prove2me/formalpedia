-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch15WronskianIndependent_rs_odd_of_norm_shell
-- name    : QseriesFormalization.Pending.Ch15WronskianIndependent.rs_odd_of_norm_shell
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T11:20:14.658849+00:00
-- url     : https://prove2.me/theorems/f0e44d0d-f833-4495-ae29-dcb2d609aa41
-- title:
--   If $A^2+B^2=4N+1$ then $A-B$ and $A+B$ are odd
-- statement:
--   For $N\in\mathbb{N}$ and integers $A,B$ with $A^2+B^2=4N+1$, both $(A-B)\bmod 2=1$ and $(A+B)\bmod 2=1$. In particular $(R,S)=(A-B,A+B)$ has both entries odd, which is used to relate norm shells to the triangular-number representation. Chapter 15.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 15. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean#L5409-L5434

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

/-! ## Explicit coefficient reindexing maps -/

/-! ## Coefficientwise Wronskian reduction to Jacobi cube -/

/-! ### Wide norm shells for 5-recurrence bookkeeping -/

theorem QseriesFormalization.Pending.Ch15WronskianIndependent.rs_odd_of_norm_shell {N : ℕ} {A B : ℤ}
    (h : A ^ 2 + B ^ 2 = 4 * (N : ℤ) + 1) :
    (A - B) % 2 = 1 ∧ (A + B) % 2 = 1 := by sorry
