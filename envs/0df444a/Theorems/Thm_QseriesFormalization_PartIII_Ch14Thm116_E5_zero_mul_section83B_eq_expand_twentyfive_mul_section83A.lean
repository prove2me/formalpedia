-- Prove2me | Theorems.Thm_QseriesFormalization_PartIII_Ch14Thm116_E5_zero_mul_section83B_eq_expand_twentyfive_mul_section83A
-- name    : QseriesFormalization.PartIII.Ch14Thm116.E5_zero_mul_section83B_eq_expand_twentyfive_mul_section83A
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:12:09.097295+00:00
-- url     : https://prove2.me/theorems/2534c951-5602-47a5-86e9-160643db06e1
-- title:
--   $E_0\cdot B=(q^{25};q^{25})_\infty\cdot A$ in $\mathbb{C}[[X]]$
-- statement:
--   In $\mathbb{C}[[X]]$, with $E_0$ the residue-$0$ section of $(q;q)_\infty$ modulo $5$, $(q^{25};q^{25})_\infty$ the series $(q;q)_\infty$ with $X\mapsto X^{25}$, and $A,B$ the two theta series of section 8.3 (each being a mod-5 theta series with $X\mapsto X^5$),
--   $$E_0\cdot B=(q^{25};q^{25})_\infty\cdot A.$$
--   This relation (stated with an unused primitive-fifth-root hypothesis) is one ingredient in the proof of Chan's Theorem 11.6.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 14. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter14_Thm116.lean#L563 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefQuintic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.ZMod.Basic

/-!
# Chapter 14 — Chan Theorem 11.6 formal target

This file records the formal-power-series objects for the Lost Notebook
identity in Chan Theorem 11.6 and closes the reusable JTP-at-a-fifth-root
denominator collapse.  The remaining unproved bridge is isolated as a single
product identity involving the Rogers-Ramanujan `G,H` product factors below.
-/

open QseriesFormalization

open PowerSeries
open Filter
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.RamanujanQuintic
open QseriesFormalization.Pending.RamanujanQuinticJTP
open QseriesFormalization.Pending.Ch16MBIProof

/-! ## The four product-side series in Theorem 11.6 -/

/-! ## Period normalizations for a primitive fifth root -/

/-! ## Product rewrites for the §8.3 factors -/

/-! ## The JTP denominator collapse reused by Theorem 11.6 -/

/-! ## Unit bookkeeping for the reciprocal side -/

/-! ## Closing the remaining product bridge -/

theorem QseriesFormalization.PartIII.Ch14Thm116.E5_zero_mul_section83B_eq_expand_twentyfive_mul_section83A
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    E5 ℂ 0 * section83B ℂ =
      PowerSeries.expand 25 (by decide) (qPochInfPS ℂ) * section83A ℂ := by sorry
