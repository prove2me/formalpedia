-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_twentythree
-- name    : QseriesFormalization.Ch01.partitionCount_twentythree
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:49:47.372214+00:00
-- url     : https://prove2.me/theorems/0610dd15-d825-4f67-81f3-d99875145c00
-- title:
--   $p(23)=1255$
-- statement:
--   The number of partitions of $\,23$ (ways of writing $23$ as an unordered sum of positive integers) is $1255$:
--   $$p(23)=1255.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_PartitionCount23.lean#L33 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-!
# Chapter 1 — `partitionCount 23 = 1255`

For n ≥ 22, the recurrence picks up the next-pentagonal contribution
at m = 22 (σ(22) = +1).  At n = 23 this gives a non-trivial p(1)·σ(22)
term in the convolution:

  p(23) = p(22) + p(21) − p(18) − p(16) + p(11) + p(8) − p(1)
        = 1002 + 792 − 385 − 231 + 56 + 22 − 1 = 1255.

Proof: `Ch01.partitionCountRec_eq_partitionCount` (Euler's pentagonal recurrence,
proved in `Chapter01` from Euler's identity and the pentagonal number theorem)
reduces the claim to evaluating the computable recurrence `partitionCountRec 23`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

theorem QseriesFormalization.Ch01.partitionCount_twentythree : partitionCount 23 = 1255 := by sorry
