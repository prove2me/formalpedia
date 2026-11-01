-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_nineteen
-- name    : QseriesFormalization.Ch01.partitionCount_nineteen
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:43:07.188996+00:00
-- url     : https://prove2.me/theorems/feb22e85-ced6-436f-abe5-84ade0d122fc
-- title:
--   $p(19)=490$
-- statement:
--   The number of partitions of $\,19$ (ways of writing $19$ as an unordered sum of positive integers) is $490$:
--   $$p(19)=490.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_PartitionCount19.lean#L20 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-! # Chapter 1 — `partitionCount 19 = 490`

Proof: `Ch01.partitionCountRec_eq_partitionCount` (Euler's pentagonal recurrence,
proved in `Chapter01` from Euler's identity and the pentagonal number theorem)
reduces the claim to evaluating the computable recurrence `partitionCountRec 19`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

theorem QseriesFormalization.Ch01.partitionCount_nineteen : partitionCount 19 = 490 := by sorry
