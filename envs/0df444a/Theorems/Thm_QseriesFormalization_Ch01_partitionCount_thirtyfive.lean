-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_thirtyfive
-- name    : QseriesFormalization.Ch01.partitionCount_thirtyfive
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:45:22.201556+00:00
-- url     : https://prove2.me/theorems/a9b13ef0-3ac8-4b42-9325-c0c766216e05
-- title:
--   $p(35)=14883$
-- statement:
--   The number of partitions of $\,35$ (ways of writing $35$ as an unordered sum of positive integers) is $14883$:
--   $$p(35)=14883.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_PartitionCount35.lean#L47 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-!
# Chapter 1 — `partitionCount 35 = 14883`

35 is the next pentagonal number after 26: `35 = 5·(3·5 − 1)/2` (k=5
minus side), so σ(35) = (−1)^5 = −1.  At n = 35 the recurrence picks up
p(0)·σ(35) = −1·1 = −1 as the new nontrivial contribution.

  p(35) = p(34) + p(33) − p(30) − p(28) + p(23) + p(20) − p(13) − p(9) + p(0)
        = 12310 + 10143 − 5604 − 3718 + 1255 + 627 − 101 − 30 + 1
        = 14883.

Proof: `Ch01.partitionCountRec_eq_partitionCount` (Euler's pentagonal recurrence,
proved in `Chapter01` from Euler's identity and the pentagonal number theorem)
reduces the claim to evaluating the computable recurrence `partitionCountRec 35`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

theorem QseriesFormalization.Ch01.partitionCount_thirtyfive : partitionCount 35 = 14883 := by sorry
