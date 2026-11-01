-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSMod7_summable_theta7ThetaTerm
-- name    : QseriesFormalization.Pending.JTPFormalPSMod7.summable_theta7ThetaTerm
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:29:18.400389+00:00
-- url     : https://prove2.me/theorems/f817f48c-1552-4984-b47e-52efdd78bc27
-- title:
--   Absolute convergence of the mod 7 theta terms for $|q|<1$
-- statement:
--   Let $c\in\{1,3,5\}$ (`ThetaCValid`) and $q\in\mathbb{C}$ with $\|q\|<1$. The family $k\mapsto(-1)^kq^{\mathrm{theta7Exp}\,c\,k}$, $k\in\mathbb{Z}$, is summable. Chapter 17 support for the analytic-to-formal bridge.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Mod7.lean#L244-L273

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

/-! ## Bilateral theta analytic-to-formal bridge -/

theorem QseriesFormalization.Pending.JTPFormalPSMod7.summable_theta7ThetaTerm {c : ℤ} (hc : ThetaCValid c) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun k : ℤ => theta7ThetaTerm c q k := by sorry
