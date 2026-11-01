-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_ASDEtaProducts_A0_eq_asd5FProductPS_zmod5
-- name    : QseriesFormalization.Pending.ASDEtaProducts.A0_eq_asd5FProductPS_zmod5
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:35:29.71502+00:00
-- url     : https://prove2.me/theorems/5ad61205-9dc9-4593-880d-81f5f14db433
-- title:
--   Residue-0 part of $(q;q)_\infty^3$ mod 5 is the eta product $F=(q^{10},q^{15},q^{25};q^{25})_\infty$
-- statement:
--   Over $\mathbb{Z}/5$, let $A_0$ be the part of $(q;q)_\infty^3$ (`qPochInfPS`) supported on exponents $\equiv0\bmod 5$ (`A 0`, keeping coefficients, no compression). Then
--   $$A_0=F:=\prod_{n\ge0}(1-X^{10+25n})(1-X^{15+25n})(1-X^{25+25n}),$$
--   Hirschhorn's $F(q^5)$ (`asd5FProductPS`). Chapter 17.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/ASD_EtaProducts.lean#L562-L564

import Definitions.Def_QseriesFormalization_Pending_Chapter17_ASD_Mod5
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
namespace QseriesFormalization.Pending.ASDMod5Full end QseriesFormalization.Pending.ASDMod5Full

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

theorem QseriesFormalization.Pending.ASDEtaProducts.A0_eq_asd5FProductPS_zmod5 :
    A 0 = asd5FProductPS (ZMod 5) := by sorry
