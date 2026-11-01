-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSMod7_one_sixteenth_le_mod7ProductCoeffFMLS_radius
-- name    : QseriesFormalization.Pending.JTPFormalPSMod7.one_sixteenth_le_mod7ProductCoeffFMLS_radius
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:28:47.700984+00:00
-- url     : https://prove2.me/theorems/da4d310a-d08e-425a-97be-15990819b440
-- title:
--   Taylor series of the mod 7 product has radius at least $1/16$
-- statement:
--   For natural numbers $a,b>0$, the power series with coefficients $[X^n]\,(q^a,q^b,q^7;q^7)_\infty$ over $\mathbb{C}$ (`mod7ProductCoeffFMLS`) has radius of convergence at least $1/16$. A small-disc estimate, Chapter 17 support.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Mod7.lean#L949-L970

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

/-! ## Analytic JTP specialisations for modulus 7 -/

/-! ## Product coefficient Taylor bridge -/

theorem QseriesFormalization.Pending.JTPFormalPSMod7.one_sixteenth_le_mod7ProductCoeffFMLS_radius
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ((1 / 16 : NNReal) : ENNReal) ≤ (mod7ProductCoeffFMLS a b).radius := by sorry
