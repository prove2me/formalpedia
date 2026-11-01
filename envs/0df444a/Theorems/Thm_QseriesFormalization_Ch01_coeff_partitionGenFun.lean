-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_coeff_partitionGenFun
-- name    : QseriesFormalization.Ch01.coeff_partitionGenFun
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:37:11.697168+00:00
-- url     : https://prove2.me/theorems/105d9194-3602-47f3-b381-942bbfae8464
-- title:
--   Coefficients of the partition generating series are $p(n)$
-- statement:
--   For every natural number $n$, the coefficient of $X^n$ in the integer-coefficient partition generating series $\mathrm{partitionGenFun}\,\mathbb{Z}\in\mathbb{Z}[[X]]$ equals $p(n)$, the number of partitions of $n$:
--   $$[X^n]\,\mathrm{partitionGenFun}\,\mathbb{Z}=p(n).$$
--   This is the coefficient form of Euler's generating function (1.1) in Chapter 1, relating the series defined in the Chapter 19 development to the combinatorial count.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_GenFun.lean#L27-L34

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

theorem QseriesFormalization.Ch01.coeff_partitionGenFun (n : Nat) :
    (PartIV.Ch19.partitionGenFun ℤ).coeff n = (partitionCount n : ℤ) := by sorry
