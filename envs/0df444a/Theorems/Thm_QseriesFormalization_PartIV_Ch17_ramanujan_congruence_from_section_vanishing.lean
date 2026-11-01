-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_ramanujan_congruence_from_section_vanishing
-- name    : QseriesFormalization.PartIV.Ch17.ramanujan_congruence_from_section_vanishing
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:44:49.979184+00:00
-- url     : https://prove2.me/theorems/06db3de6-8ca4-4eb0-b491-2b48486a80d1
-- title:
--   Ramanujan-type congruence from vanishing of the $(p,r)$-section (conditional)
-- statement:
--   Let $p$ be a prime and $r\in\mathbb{N}$. Assume the $(p,r)$-section of the partition generating function over $\mathbb{Z}/p$ is zero (hypothesis `h`). Then for all $n\in\mathbb{N}$, $p\mid p(pn+r)$ as natural numbers. This is a conditional statement: it does not prove the hypothesis for any particular $(p,r)$. It is the entry point from the formal-series side to the integer congruence in Chapter 17.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17_SectionBridge.lean#L60-L73

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

theorem QseriesFormalization.PartIV.Ch17.ramanujan_congruence_from_section_vanishing
    (p : Nat) [Fact (Nat.Prime p)] (r : Nat)
    (h : section_kr (ZMod p) p r (partitionGenFun (ZMod p)) = 0) :
    ∀ n, p ∣ QseriesFormalization.Ch01.partitionCount (p * n + r) := by sorry
