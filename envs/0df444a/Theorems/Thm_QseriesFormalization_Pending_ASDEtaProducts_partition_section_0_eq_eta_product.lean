-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_ASDEtaProducts_partition_section_0_eq_eta_product
-- name    : QseriesFormalization.Pending.ASDEtaProducts.partition_section_0_eq_eta_product
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:37:06.412336+00:00
-- url     : https://prove2.me/theorems/6bcbdc31-4b12-40a4-8113-7a7d0479c2b2
-- title:
--   Section of $P$ at $5n$ mod 5: $\sum p(5n)X^n\equiv\mathrm{section}_{5,0}(F^3)\cdot P^2$
-- statement:
--   Over $\mathbb{Z}/5$, let $P$ be the partition generating function (`partitionGenFun`), $F=(q^{10},q^{15},q^{25};q^{25})_\infty$ (`asd5FProductPS`) and $\mathrm{section}_{5,0}\varphi=\sum_n[X^{5n}]\varphi\,X^n$ (`section_kr`). Then
--   $$\mathrm{section}_{5,0}(P)=\mathrm{section}_{5,0}(F^3)\cdot P^2,$$
--   i.e. $\sum_np(5n)X^n\equiv \mathrm{section}_{5,0}(F^3)/(q;q)_\infty^2\pmod5$ at the series level, in Hirschhorn's notation. Chapter 17.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/ASD_EtaProducts.lean#L953-L957

import Definitions.Def_QseriesFormalization_Chapter19_Section5
import Definitions.Def_QseriesFormalization_Pending_Chapter17_ASD_Mod5_Full
import Definitions.Def_QseriesFormalization_DefQuintic
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

namespace QseriesFormalization.PartIV.Ch17 end QseriesFormalization.PartIV.Ch17

/-!
# ASD eta-product formal identities

This file records the modulus-25 eta-product identities obtained from the
closed mod-5 formal Jacobi triple product identities by the substitution
`X ↦ X^5`.
-/

open QseriesFormalization
open QseriesFormalization.Pending
open QseriesFormalization.Pending.ASDEtaProducts

open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology

open JTPFormalPSPentagonal
open QseriesFormalization.PartIV.Ch19

/-! ## Expanding AP products -/

/-! ## Hirschhorn §3.6.5: the mod-25 F/G eta products -/

/-! ## Integral and mod-5 forms of the two JTP product identities -/

/-!
## Section-to-eta bridge, conditional on the remaining A-section identifications

The hard coefficient-level gap left by this file is the identification
`A 0 = F(q^5)` and `A 1 = -3qG(q^5)` in `ZMod 5`.  The following lemmas
show that once those two identifications are supplied, the section-form ASD
congruences from `Chapter17_ASD_Mod5_Full` immediately rewrite to the
eta-product form.
-/

open QseriesFormalization.Pending.ASDMod5
open QseriesFormalization.Pending.ASDMod5Full
open QseriesFormalization.PartIV.Ch17

/-! ### UNCONDITIONAL ASD mod-5 η-quotient congruences (Hirschhorn 3.6.7)

The `A 0 = F`, `A 1 = -3qG` identifications are now theorems
(`A0_eq_asd5FProductPS_zmod5`, `A1_eq_asd5GShiftedProductPS_zmod5`), so the
conditional forms above become unconditional. -/

theorem QseriesFormalization.Pending.ASDEtaProducts.partition_section_0_eq_eta_product :
    section_kr (ZMod 5) 5 0 P5 =
      section_kr (ZMod 5) 5 0 ((asd5FProductPS (ZMod 5)) ^ 3) * P5 ^ 2 := by sorry
