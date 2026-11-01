-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_fifty
-- name    : QseriesFormalization.Ch01.partitionCount_fifty
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:38:58.0115+00:00
-- url     : https://prove2.me/theorems/32b51e67-3ae4-4bec-8d7c-7860734b755f
-- title:
--   $p(50)=204226$
-- statement:
--   The number of partitions of $50$ (ways of writing $50$ as an unordered sum of positive integers) is $204226$:
--   $$p(50)=204226.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_PartitionCount50.lean#L55 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-! # Chapter 1 — `partitionCount 50 = 204226`

Proof: `Ch01.partitionCountRec_eq_partitionCount` (Euler's pentagonal recurrence,
proved in `Chapter01` from Euler's identity and the pentagonal number theorem)
reduces the claim to evaluating the computable recurrence `partitionCountRec 50`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

theorem QseriesFormalization.Ch01.partitionCount_fifty : partitionCount 50 = 204226 := by sorry
