-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSMod7_one_le_theta7SeriesFMLS_radius
-- name    : QseriesFormalization.Pending.JTPFormalPSMod7.one_le_theta7SeriesFMLS_radius
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:28:28.404522+00:00
-- url     : https://prove2.me/theorems/690f2696-cecd-429a-8030-71602a58f6c2
-- title:
--   Radius of convergence of the mod 7 theta series is at least 1
-- statement:
--   Let $c\in\{1,3,5\}$ (`ThetaCValid`). The formal multilinear (power) series over $\mathbb{C}$ with coefficients `theta7Coeff` $c\,\mathbb{C}\,n$ has radius of convergence at least $1$. Chapter 17 support.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Mod7.lean#L310-L331

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

theorem QseriesFormalization.Pending.JTPFormalPSMod7.one_le_theta7SeriesFMLS_radius {c : ℤ} (hc : ThetaCValid c) :
    (1 : ENNReal) ≤ (theta7SeriesFMLS c).radius := by sorry
