-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch13Eq1237_mod5_product_core_atFive_of_E5_denominator_identity
-- name    : QseriesFormalization.Pending.Ch13Eq1237.mod5_product_core_atFive_of_E5_denominator_identity
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T11:05:29.2347+00:00
-- url     : https://prove2.me/theorems/4cb9aa8b-8ff5-499c-bf50-a9e1b165771d
-- title:
--   Reduction: mod-5 product-core identity follows from an $E_5$ denominator identity (hypothesis supplied)
-- statement:
--   Let $E(q)=(q;q)_\infty$ and let $D=E_0^5+11E_1^5+E_2^5$ (with $E_r$ the mod-5 sections of $E$). Assume $$D\cdot E(q^{25})=E(q^5)^6\quad\text{in }\mathbb{Q}[[X]].$$ Then, with $P_{014}^{(5)},P_{023}^{(5)}$ the $(q^5,q^{20},q^{25};q^{25})_\infty$ and $(q^{10},q^{15},q^{25};q^{25})_\infty$ products and $C=(P_{023}^{(5)})^{10}-11X^5(P_{014}^{(5)})^5(P_{023}^{(5)})^5-X^{10}(P_{014}^{(5)})^{10}$, $$E(q^{25})^6\,C=E(q^5)^6\,(P_{014}^{(5)})^5(P_{023}^{(5)})^5.$$ A conditional statement; the denominator identity is a hypothesis. Chapter 13 (Eq. 12.37-type argument).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 13. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter13_Eq1237.lean#L20-L104

import Definitions.Def_QseriesFormalization_DefQuintic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.ZMod.Basic

/-!
# Chan Equation 12.37 in formal power series

This file packages the product-core identity already implicit in the closed
Macdonald-Bailey / Ramanujan-quintic proof.
-/

open QseriesFormalization
open QseriesFormalization.Pending

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Ch16MBIProof
open QseriesFormalization.Pending.JTPFormalPSPentagonal

theorem QseriesFormalization.Pending.Ch13Eq1237.mod5_product_core_atFive_of_E5_denominator_identity
    (hden :
      E5DenominatorCoreRat *
          PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) =
        (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6) :
    (PowerSeries.expand 25 (by decide) (qPochInfPS ℚ))^6 *
        ramanujanMod5ProductCoreRat =
      (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
        (pentagonalProduct014AtFiveRat)^5 *
        (pentagonalProduct023AtFiveRat)^5 := by sorry
