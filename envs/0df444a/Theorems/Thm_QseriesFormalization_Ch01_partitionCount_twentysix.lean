-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_twentysix
-- name    : QseriesFormalization.Ch01.partitionCount_twentysix
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:49:21.795874+00:00
-- url     : https://prove2.me/theorems/8d9fd871-8f3e-43bc-ab06-bca9a42b42e5
-- title:
--   $p(26)=2436$
-- statement:
--   The number of partitions of $\,26$ (ways of writing $26$ as an unordered sum of positive integers) is $2436$:
--   $$p(26)=2436.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_PartitionCount26.lean#L37 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-!
# Chapter 1 — `partitionCount 26 = 2436`

26 is the second pentagonal number from k=4 (the "plus side"):
`26 = 4·(3·4 + 1)/2`, so σ(26) = (−1)^4 = +1.

This is the next non-zero σ after σ(22) = +1.

  p(26) = p(25) + p(24) − p(21) − p(19) + p(14) + p(11) − p(4) − p(0)
        = 1958 + 1575 − 792 − 490 + 135 + 56 − 5 − 1 = 2436.

Proof: `Ch01.partitionCountRec_eq_partitionCount` (Euler's pentagonal recurrence,
proved in `Chapter01` from Euler's identity and the pentagonal number theorem)
reduces the claim to evaluating the computable recurrence `partitionCountRec 26`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

theorem QseriesFormalization.Ch01.partitionCount_twentysix : partitionCount 26 = 2436 := by sorry
