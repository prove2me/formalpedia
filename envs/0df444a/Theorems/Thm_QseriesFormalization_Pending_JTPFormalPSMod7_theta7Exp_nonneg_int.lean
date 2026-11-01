-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSMod7_theta7Exp_nonneg_int
-- name    : QseriesFormalization.Pending.JTPFormalPSMod7.theta7Exp_nonneg_int
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:29:55.35153+00:00
-- url     : https://prove2.me/theorems/ea8f0b3f-f02d-48e1-b09b-22b6c01d41f5
-- title:
--   Exponent $k(7k-c)/2$ is nonnegative for $c\in\{1,3,5\}$
-- statement:
--   Let $c\in\{1,3,5\}$ (`ThetaCValid`) and $k\in\mathbb{Z}$. Then $0\le k(7k-c)/2$ (integer division). This guarantees that the exponents $(7k^2-ck)/2$ of the bilateral theta series $\sum_k(-1)^kX^{(7k^2-ck)/2}$ are genuine natural numbers. Used for the mod 7 theta series supporting Chapter 17.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Mod7.lean#L138-L152

import Definitions.Def_QseriesFormalization_Pending_JTP_FormalPS_Mod7
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith

namespace QseriesFormalization.Pending.ASDEtaProducts end QseriesFormalization.Pending.ASDEtaProducts

/-!
# Formal power-series shells for the mod-7 JTP specialisations

This file mirrors the completed mod-5 path in
`Pending/JTP_FormalPS_Pentagonal.lean` and `Pending/ASD_EtaProducts.lean`.
It keeps all declarations local to this new pending file.
-/

open QseriesFormalization
open QseriesFormalization.Pending
open QseriesFormalization.Pending.JTPFormalPSMod7

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology

open JTPFormalPSPentagonal
open ASDEtaProducts

/-! ## Analytic mod-7 AP factors -/

/-! ## Formal AP products -/

/-! ## Formal bilateral theta coefficients -/

theorem QseriesFormalization.Pending.JTPFormalPSMod7.theta7Exp_nonneg_int {c : ℤ} (hc : ThetaCValid c) (k : ℤ) :
    0 ≤ k * (7 * k - c) / 2 := by sorry
