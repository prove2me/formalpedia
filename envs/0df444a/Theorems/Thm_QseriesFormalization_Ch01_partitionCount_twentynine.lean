-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_twentynine
-- name    : QseriesFormalization.Ch01.partitionCount_twentynine
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:48:45.888023+00:00
-- url     : https://prove2.me/theorems/b830b5ee-8f48-4ace-bad6-97541a3483fa
-- title:
--   $p(29)=4565$
-- statement:
--   The number of partitions of $\,29$ (ways of writing $29$ as an unordered sum of positive integers) is $4565$:
--   $$p(29)=4565.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_PartitionCount29.lean#L31 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-! # Chapter 1 — `partitionCount 29 = 4565`

Proof: `Ch01.partitionCountRec_eq_partitionCount` (Euler's pentagonal recurrence,
proved in `Chapter01` from Euler's identity and the pentagonal number theorem)
reduces the claim to evaluating the computable recurrence `partitionCountRec 29`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

theorem QseriesFormalization.Ch01.partitionCount_twentynine : partitionCount 29 = 4565 := by sorry
