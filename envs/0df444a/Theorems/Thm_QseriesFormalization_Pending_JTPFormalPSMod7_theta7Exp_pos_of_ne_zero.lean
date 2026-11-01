-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSMod7_theta7Exp_pos_of_ne_zero
-- name    : QseriesFormalization.Pending.JTPFormalPSMod7.theta7Exp_pos_of_ne_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:30:22.493194+00:00
-- url     : https://prove2.me/theorems/6fd3b87d-fa77-4a25-b721-b4d6ee8d2673
-- title:
--   Exponent $k(7k-c)/2$ is positive for $k\ne0$
-- statement:
--   Let $c\in\{1,3,5\}$ (`ThetaCValid`) and $k\in\mathbb{Z}$ with $k\ne0$. Then the natural number `theta7Exp` $c\,k=\lfloor k(7k-c)/2\rfloor$ is positive. Hence only $k=0$ contributes to the constant term of the mod 7 theta series. Chapter 17 support.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Mod7.lean#L202-L218

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

theorem QseriesFormalization.Pending.JTPFormalPSMod7.theta7Exp_pos_of_ne_zero {c : ℤ} (hc : ThetaCValid c) {k : ℤ}
    (hk : k ≠ 0) :
    0 < theta7Exp c k := by sorry
