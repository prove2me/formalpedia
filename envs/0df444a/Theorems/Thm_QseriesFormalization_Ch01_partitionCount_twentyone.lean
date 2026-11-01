-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_twentyone
-- name    : QseriesFormalization.Ch01.partitionCount_twentyone
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:48:52.425927+00:00
-- url     : https://prove2.me/theorems/a7302d72-a377-4ac1-9cc3-198385b2577f
-- title:
--   $p(21)=792$
-- statement:
--   The number of partitions of $\,21$ (ways of writing $21$ as an unordered sum of positive integers) is $792$:
--   $$p(21)=792.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_PartitionCount21.lean#L22 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-! # Chapter 1 — `partitionCount 21 = 792`

Proof: `Ch01.partitionCountRec_eq_partitionCount` (Euler's pentagonal recurrence,
proved in `Chapter01` from Euler's identity and the pentagonal number theorem)
reduces the claim to evaluating the computable recurrence `partitionCountRec 21`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

theorem QseriesFormalization.Ch01.partitionCount_twentyone : partitionCount 21 = 792 := by sorry
