-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_ASDEtaProducts_jacobiTripleSign_five_mul_eq_pentagonal023Coeff_zmod5
-- name    : QseriesFormalization.Pending.ASDEtaProducts.jacobiTripleSign_five_mul_eq_pentagonal023Coeff_zmod5
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:36:35.212208+00:00
-- url     : https://prove2.me/theorems/31f02794-c069-444c-9e21-9ec0042c0a2d
-- title:
--   Jacobi sign at $5m$ equals the bilateral pentagonal coefficient mod 5
-- statement:
--   Let $J$ = `jacobiTripleSign` ($J(n)=(-1)^k(2k+1)$ if $n=k(k+1)/2$, else $0$). For every $m\in\mathbb{N}$, in $\mathbb{Z}/5$,
--   $$J(5m)=[X^m]\sum_{k\in\mathbb{Z}}(-1)^kX^{k(5k-1)/2},$$
--   i.e. `pentagonal023Coeff` $(\mathbb{Z}/5)\,m$, the signed count of integers $k$ with $k(5k-1)/2=m$. A coefficient identification in the Hirschhorn-style mod 5 analysis of Chapter 17.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/ASD_EtaProducts.lean#L441-L538

import Definitions.Def_QseriesFormalization_DefCoreQSeries
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
namespace QseriesFormalization.Pending.ASDMod5 end QseriesFormalization.Pending.ASDMod5
namespace QseriesFormalization.Pending.ASDMod5Full end QseriesFormalization.Pending.ASDMod5Full

/-!
# ASD eta-product formal identities

This file records the modulus-25 eta-product identities obtained from the
closed mod-5 formal Jacobi triple product identities by the substitution
`X ↦ X^5`.
-/

open QseriesFormalization
open QseriesFormalization.Pending

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

theorem QseriesFormalization.Pending.ASDEtaProducts.jacobiTripleSign_five_mul_eq_pentagonal023Coeff_zmod5 (m : ℕ) :
    ((jacobiTripleSign (5 * m) : ℤ) : ZMod 5) =
      pentagonal023Coeff (ZMod 5) m := by sorry
