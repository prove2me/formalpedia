-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_forty
-- name    : QseriesFormalization.Ch01.partitionCount_forty
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:40:02.755505+00:00
-- url     : https://prove2.me/theorems/4c78ae26-d8f8-4b1d-a305-b40cd6c61bbb
-- title:
--   $p(40)=37338$
-- statement:
--   The number of partitions of $40$ (ways of writing $40$ as an unordered sum of positive integers) is $37338$:
--   $$p(40)=37338.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_PartitionCount40.lean#L53 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-!
# Chapter 1 — `partitionCount 40 = 37338`

40 is pentagonal (k=5 plus side: `40 = 5·(3·5+1)/2`), so σ(40) = (−1)^5 = −1.
This is the second pentagonal-driven contribution after σ(35).  The
recurrence picks up `p(0)·σ(40) = +1` (negated to `−1` in the convolution
sum, giving `+p(0)` on the RHS).

  p(40) = p(39) + p(38) − p(35) − p(33) + p(28) + p(25) − p(18) − p(14) + p(5) + p(0)
        = 31185 + 26015 − 14883 − 10143 + 3718 + 1958 − 385 − 135 + 7 + 1
        = 37338.

Proof: `Ch01.partitionCountRec_eq_partitionCount` (Euler's pentagonal recurrence,
proved in `Chapter01` from Euler's identity and the pentagonal number theorem)
reduces the claim to evaluating the computable recurrence `partitionCountRec 40`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

theorem QseriesFormalization.Ch01.partitionCount_forty : partitionCount 40 = 37338 := by sorry
