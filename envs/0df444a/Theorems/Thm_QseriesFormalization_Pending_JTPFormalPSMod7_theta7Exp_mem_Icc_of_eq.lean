-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSMod7_theta7Exp_mem_Icc_of_eq
-- name    : QseriesFormalization.Pending.JTPFormalPSMod7.theta7Exp_mem_Icc_of_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:29:43.164128+00:00
-- url     : https://prove2.me/theorems/a9df3dd8-868d-4044-a5a0-32ef1f3aa80b
-- title:
--   Index bound: $\mathrm{theta7Exp}\,c\,k=n$ forces $|k|\le n+1$
-- statement:
--   Let $c\in\{1,3,5\}$ (`ThetaCValid`), $k\in\mathbb{Z}$ and $n\in\mathbb{N}$. If `theta7Exp` $c\,k=n$ (the natural number $\lfloor k(7k-c)/2\rfloor$), then $-(n+1)\le k\le n+1$. This justifies truncating the sum defining `theta7Coeff` to a finite range. Chapter 17 support.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Mod7.lean#L177-L200

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

theorem QseriesFormalization.Pending.JTPFormalPSMod7.theta7Exp_mem_Icc_of_eq {c : ℤ} (hc : ThetaCValid c)
    {k : ℤ} {n : ℕ} (h : theta7Exp c k = n) :
    k ∈ Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ) := by sorry
