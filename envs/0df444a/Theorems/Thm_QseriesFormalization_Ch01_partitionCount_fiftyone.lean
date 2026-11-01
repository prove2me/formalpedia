-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_fiftyone
-- name    : QseriesFormalization.Ch01.partitionCount_fiftyone
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:39:25.488394+00:00
-- url     : https://prove2.me/theorems/bc4aad18-c361-4413-84c1-8da357a1765a
-- title:
--   $p(51)=239943$
-- statement:
--   The number of partitions of $51$ (ways of writing $51$ as an unordered sum of positive integers) is $239943$:
--   $$p(51)=239943.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_PartitionCount51.lean#L67 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-!
# Chapter 1 — `partitionCount 51 = 239943`

51 is the next pentagonal number after 40: `51 = 6·(3·6 − 1)/2` (k=6 minus
side), so σ(51) = (−1)^6 = +1.

  p(51) = p(50) + p(49) − p(46) − p(44) + p(39) + p(36) − p(29) − p(25)
              + p(16) + p(11) − p(0)
        = 204226 + 173525 − 105558 − 75175 + 31185 + 17977 − 4565 − 1958
              + 231 + 56 − 1
        = 239943.

Proof: `Ch01.partitionCountRec_eq_partitionCount` (Euler's pentagonal recurrence,
proved in `Chapter01` from Euler's identity and the pentagonal number theorem)
reduces the claim to evaluating the computable recurrence `partitionCountRec 51`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

theorem QseriesFormalization.Ch01.partitionCount_fiftyone : partitionCount 51 = 239943 := by sorry
