-- Prove2me | Theorems.Thm_QseriesFormalization_PartIII_Ch14Thm116_chan116RHS_period_mul_section83_rhs_pair14
-- name    : QseriesFormalization.PartIII.Ch14Thm116.chan116RHS_period_mul_section83_rhs_pair14
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:13:06.765777+00:00
-- url     : https://prove2.me/theorems/36950e0f-339b-42cb-8034-184f5f779ac4
-- title:
--   The Theorem 11.6 right side times the collapsed denominator equals $(q;q)_\infty^2$
-- statement:
--   Let $\zeta\in\mathbb{C}$ be a primitive fifth root of unity. In $\mathbb{C}[[X]]$, let $\mathrm{RHS}$ be the four-term right side of Chan's Theorem 11.6, written with the Gaussian periods $\alpha=\zeta+\zeta^4$, $\beta=\zeta^2+\zeta^3$ as $A-\alpha^2XB+\beta X^2C-\alpha X^3D$, and let $A_0+\beta XB_0$ be the two-term series of section 8.3 (equal to $(q,\zeta q,\zeta^{-1}q;q)_\infty$). Then
--   $$\mathrm{RHS}\cdot\big(A_0+\beta XB_0\big)=(q;q)_\infty^{2}.$$
--   Chan's Theorem 11.6 reads (formally) $\dfrac{(q;q)_\infty}{(\zeta q;q)_\infty(\zeta^{-1}q;q)_\infty}=A-(\zeta+\zeta^{-1})^2qB+(\zeta^2+\zeta^{-2})q^2C-(\zeta+\zeta^{-1})q^3D$, where $A=f(-q^{25})G(q^5)^2/H(q^5)$, $B=f(-q^{25})G(q^5)$, $C=f(-q^{25})H(q^5)$, $D=f(-q^{25})H(q^5)^2/G(q^5)$, $G,H$ being the Rogers-Ramanujan products and $f(-q^{25})=(q^{25};q^{25})_\infty$. This is the algebraic core of the proof of Theorem 11.6.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 14. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter14_Thm116.lean#L1004-L1064

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

theorem QseriesFormalization.PartIII.Ch14Thm116.chan116RHS_period_mul_section83_rhs_pair14
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    chan116RHS_period ζ * section83_rhs_pair14 ζ = (qPochInfPS ℂ)^2 := by sorry
