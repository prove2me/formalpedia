-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch15WronskianIndependent_apSigmaLambertFactor_eq_etaQuotient_iff_mul_expandFive
-- name    : QseriesFormalization.Pending.Ch15WronskianIndependent.apSigmaLambertFactor_eq_etaQuotient_iff_mul_expandFive
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T11:10:44.297274+00:00
-- url     : https://prove2.me/theorems/5df1796e-3628-4a25-9bdf-80fd7845388e
-- title:
--   Equivalence of divided and multiplied forms: $\Lambda=E^5/E(q^5)\iff\Lambda\,E(q^5)=E^5$
-- statement:
--   Let $\Lambda=1+5\big((\sigma_{2,5}+\sigma_{3,5})-(\sigma_{1,5}+\sigma_{4,5})\big)\in\mathbb{Q}[[X]]$, $E=(q;q)_\infty$ and $E(q^5)=(X^5;X^5)_\infty$. Then $$\Lambda=E^5\cdot E(q^5)^{-1}\iff\Lambda\cdot E(q^5)=E^5.$$ Equivalent because $E(q^5)$ is a unit. Chapter 15.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 15. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean#L508-L527

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

theorem QseriesFormalization.Pending.Ch15WronskianIndependent.apSigmaLambertFactor_eq_etaQuotient_iff_mul_expandFive :
    (apSigmaLambertFactor =
        (qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹) ↔
      (apSigmaLambertFactor * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5) := by sorry
