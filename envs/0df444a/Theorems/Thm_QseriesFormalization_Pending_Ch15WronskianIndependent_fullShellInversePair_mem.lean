-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch15WronskianIndependent_fullShellInversePair_mem
-- name    : QseriesFormalization.Pending.Ch15WronskianIndependent.fullShellInversePair_mem
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T11:10:46.105477+00:00
-- url     : https://prove2.me/theorems/86bf6a8c-be06-446b-9a6b-64437ff6132a
-- title:
--   The Jacobi-pair inverse of an element of the full norm shell is a valid triangular pair
-- statement:
--   For $N\in\mathbb{N}$ and $z=(a,b)$ with $a^2+b^2=4N+1$ and $a,b\in[-(2N+1),2N+1]$, let $\mathrm{pair}(z)=\big(\lfloor(|a+b|-1)/2\rfloor,\ \lfloor(|a-b|-1)/2\rfloor\big)=(r,s)$. Then $(r,s)$ lies in the set of pairs of natural numbers $\le N$ with $T_r+T_s=N$, where $T_m=m(m+1)/2$. Chapter 15 bookkeeping for the Jacobi-cube coefficients.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 15. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean#L6001-L6046

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

/-! ## Explicit coefficient reindexing maps -/

/-! ## Coefficientwise Wronskian reduction to Jacobi cube -/

/-! ### Wide norm shells for 5-recurrence bookkeeping -/

theorem QseriesFormalization.Pending.Ch15WronskianIndependent.fullShellInversePair_mem {N : ℕ} {z : GaussianInt}
    (hz : z ∈ fullNormShell N) :
    fullShellInversePair z ∈ jacobiShellPairs N := by sorry
