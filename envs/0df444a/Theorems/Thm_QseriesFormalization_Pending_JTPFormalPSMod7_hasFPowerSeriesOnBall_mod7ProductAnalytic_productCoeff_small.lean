-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSMod7_hasFPowerSeriesOnBall_mod7ProductAnalytic_productCoeff_small
-- name    : QseriesFormalization.Pending.JTPFormalPSMod7.hasFPowerSeriesOnBall_mod7ProductAnalytic_productCoeff_small
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:25:49.454052+00:00
-- url     : https://prove2.me/theorems/ad71f60a-c7be-4e9c-94a7-4ba50a0b29bc
-- title:
--   The analytic mod 7 product is analytic on the disc $|q|<1/16$
-- statement:
--   For natural numbers $a,b>0$, the function `mod7ProductAnalytic` $a\,b$ (the analytic product $(q^a,q^b,q^7;q^7)_\infty$) has the power series with coefficients $[X^n]\,\mathrm{mod7ProductPS}(a,b,\mathbb{C})$ at $0$ on the ball of radius $1/16$ (`HasFPowerSeriesOnBall`). Chapter 17 support; only a small-radius statement.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Mod7.lean#L972 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

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

theorem QseriesFormalization.Pending.JTPFormalPSMod7.hasFPowerSeriesOnBall_mod7ProductAnalytic_productCoeff_small
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    HasFPowerSeriesOnBall (mod7ProductAnalytic a b) (mod7ProductCoeffFMLS a b) 0
      ((1 / 16 : NNReal) : ENNReal) := by sorry
