-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_JTPFormalPSMod7_hasSum_mod7ProductPS_coeff_mul_pow_of_norm_lt_one_sixteenth
-- name    : QseriesFormalization.Pending.JTPFormalPSMod7.hasSum_mod7ProductPS_coeff_mul_pow_of_norm_lt_one_sixteenth
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:26:22.419302+00:00
-- url     : https://prove2.me/theorems/0be19172-6194-4d09-8c60-61dc7263aef0
-- title:
--   Taylor series of the analytic mod 7 product converges for $|q|<1/16$
-- statement:
--   Let $a,b>0$ be natural numbers and $q\in\mathbb{C}$ with $\|q\|<1/16$. Then the series $\sum_{k\ge0}[X^k]\,\mathrm{mod7ProductPS}(a,b,\mathbb{C})\cdot q^k$ converges to the analytic product `mod7ProductAnalytic` $a\,b\,q=(q^a,q^b,q^7;q^7)_\infty$. This is only a small-disc statement; Chapter 17 support.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Mod7.lean#L896-L944

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

theorem QseriesFormalization.Pending.JTPFormalPSMod7.hasSum_mod7ProductPS_coeff_mul_pow_of_norm_lt_one_sixteenth
    (a b : ℕ) (q : ℂ) (hq : ‖q‖ < (1 / 16 : ℝ)) (ha : 0 < a) (hb : 0 < b) :
    HasSum (fun k : ℕ => (mod7ProductPS a b ℂ).coeff k * q ^ k)
      (mod7ProductAnalytic a b q) := by sorry
