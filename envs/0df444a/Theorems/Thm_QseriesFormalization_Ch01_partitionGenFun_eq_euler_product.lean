-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionGenFun_eq_euler_product
-- name    : QseriesFormalization.Ch01.partitionGenFun_eq_euler_product
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:50:36.644143+00:00
-- url     : https://prove2.me/theorems/5c5abc8a-f574-4613-9d8d-b2a115f132be
-- title:
--   Euler's product form (1.1) of the partition generating function
-- statement:
--   Let $R$ be a commutative semiring with a Hausdorff topology. Here $\mathrm{partitionGenFun}\,R=\sum_{n\ge0}p(n)X^n\in R[[X]]$ is the partition generating series, with $p(n)$ the number of partitions of $n$ mapped into $R$. Then in $R[[X]]$ (product topology)
--   $$\sum_{n\ge0}p(n)X^n=\prod_{i\ge1}\Big(1+X^{i}+X^{2i}+\cdots\Big),$$
--   written in Lean as $\prod'_{i}\big(1+\sum'_{j}X^{(i+1)(j+1)}\big)$, where each factor is the formal geometric series for $1/(1-X^{i})$.
--
--   This is the Chapter 1 statement of Euler's product formula, restated from the Chapter 19 development.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_GenFun.lean#L41-L52

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Tactic.Linarith

/-!
# Chapter 1 — Generating function for `partitionCount`

This companion file to `Chapter01.lean` exposes the chapter-main theorem
of Chan Ch 1, namely Euler's identity

    ∑_{n ≥ 0} p(n) X^n  =  ∏_{i ≥ 1} 1/(1 - X^i)            (1.1)

in the formal-power-series sense.  Both halves of (1.1) are proved in
`Chapter19.lean` (the formal-PS Ramanujan framework); this file re-exports
them under the `QseriesFormalization.Ch01` namespace so that Ch 1's
chapter-main result is visible at the chapter where Chan states it.

The dependency direction is `Ch01 ← Ch19 ← Ch01_GenFun`, which is acyclic
because `Chapter19` already imports `Chapter01` for `partitionCount`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

open PowerSeries
open scoped PowerSeries.WithPiTopology

theorem QseriesFormalization.Ch01.partitionGenFun_eq_euler_product
    (R : Type*) [CommSemiring R] [TopologicalSpace R] [T2Space R] :
    PartIV.Ch19.partitionGenFun R =
      ∏' i, ((1 : R⟦X⟧) + ∑' j, (PowerSeries.X (R := R)) ^ ((i + 1) * (j + 1))) := by sorry
