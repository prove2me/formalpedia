-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_section_kr_partitionGenFun_eq_zero_iff
-- name    : QseriesFormalization.PartIV.Ch17.section_kr_partitionGenFun_eq_zero_iff
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:45:33.146429+00:00
-- url     : https://prove2.me/theorems/7779453d-3a05-40f4-9b50-43e34b144675
-- title:
--   Section vanishing of the partition series mod $p$ iff $p\mid p(pn+r)$ for all $n$
-- statement:
--   Let $p$ be a prime and $r\in\mathbb{N}$. Let $P(X)=\sum_n p(n)X^n$ be the partition generating function over $\mathbb{Z}/p$ (`partitionGenFun`). Then the $(p,r)$-section of $P$ (the series $\sum_n p(pn+r)X^n$ over $\mathbb{Z}/p$) is zero if and only if
--   $$\forall n\in\mathbb{N},\ p(pn+r)\equiv 0\pmod p.$$
--   This is a routing lemma in Chapter 17 converting the congruence into a power-series vanishing statement.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17_SectionBridge.lean#L23-L58

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Definitions.Def_QseriesFormalization_Chapter19_Section5
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib
import Mathlib.Tactic.Linarith

/-!
# Chapter 17 — Section-operator bridge to general ∀n Ramanujan congruence

This file gives the precise iff-translation between the k-section of
`partitionGenFun (ZMod p)` vanishing and the general `∀ n, p ∣ p(p·n+r)`
Ramanujan congruence statement.

Combined with Pending/Chapter16_MBI.lean (whose formal-PS form, once
proved, directly gives the section vanishing for (p, r) = (5, 4)), this
provides the missing link from MBI to the general Ramanujan ∀n theorem.
-/

open QseriesFormalization
open QseriesFormalization.PartIV

open PowerSeries
open QseriesFormalization.PartIV.Ch19

theorem QseriesFormalization.PartIV.Ch17.section_kr_partitionGenFun_eq_zero_iff
    (p : Nat) [Fact (Nat.Prime p)] (r : Nat) :
    section_kr (ZMod p) p r (partitionGenFun (ZMod p)) = 0 ↔
    ∀ n, ((QseriesFormalization.Ch01.partitionCount (p * n + r) : Nat) : ZMod p) = 0 := by sorry
