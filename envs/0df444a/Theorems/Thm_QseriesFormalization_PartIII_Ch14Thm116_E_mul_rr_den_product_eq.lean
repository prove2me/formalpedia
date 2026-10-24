-- Prove2me | Theorems.Thm_QseriesFormalization_PartIII_Ch14Thm116_E_mul_rr_den_product_eq
-- name    : QseriesFormalization.PartIII.Ch14Thm116.E_mul_rr_den_product_eq
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:12:22.169185+00:00
-- url     : https://prove2.me/theorems/cce76950-f643-44e2-961e-fc3cf8e59f48
-- title:
--   Denominator identity linking $(q;q)_\infty$ with the Rogers-Ramanujan denominators at $q^5$
-- statement:
--   Let $\zeta\in\mathbb{C}$ be a primitive fifth root of unity (the hypothesis is not used in the identity). Write $D_G=(q^5,q^{20};q^{25})_\infty$ and $D_H=(q^{10},q^{15};q^{25})_\infty$ for the denominators of the Rogers-Ramanujan products $G(q^5)$ and $H(q^5)$, and $f(-q^{25})=(q^{25};q^{25})_\infty$. Then in $\mathbb{C}[[X]]$
--   $$(q;q)_\infty\,D_G\,D_H=f(-q^{25})\big(D_H^2-X\,D_GD_H-X^2D_G^2\big).$$
--   This is the algebraic identity behind the Rogers-Ramanujan continued-fraction relation $1/R(q)-1-R(q)=\dots$ in the proof of Chan's Theorem 11.6.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 14. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter14_Thm116.lean#L949 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

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
open QseriesFormalization.PartIII
open QseriesFormalization.PartIII.Ch14Thm116

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

open QseriesFormalization.Pending
open QseriesFormalization.Pending.Ch16MBIProof

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal

open QseriesFormalization.PartIII
open QseriesFormalization.PartIII.Ch14Thm116

open PowerSeries
open Filter
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.RamanujanQuintic
open QseriesFormalization.Pending.RamanujanQuinticJTP
open QseriesFormalization.Pending.Ch16MBIProof

theorem QseriesFormalization.PartIII.Ch14Thm116.E_mul_rr_den_product_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    qPochInfPS ℂ * rrGDenAtQ5PS * rrHDenAtQ5PS =
      fMinusQ25PS *
        (rrHDenAtQ5PS * rrHDenAtQ5PS
          - PowerSeries.X * rrGDenAtQ5PS * rrHDenAtQ5PS
          - PowerSeries.X^2 * (rrGDenAtQ5PS * rrGDenAtQ5PS)) := by sorry
