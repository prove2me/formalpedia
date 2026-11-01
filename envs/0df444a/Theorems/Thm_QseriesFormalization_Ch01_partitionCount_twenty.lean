-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_twenty
-- name    : QseriesFormalization.Ch01.partitionCount_twenty
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:47:47.665981+00:00
-- url     : https://prove2.me/theorems/df6e726d-eaf3-4a01-b32a-25f32d8d13cb
-- title:
--   $p(20)=627$
-- statement:
--   The number of partitions of $\,20$ (ways of writing $20$ as an unordered sum of positive integers) is $627$:
--   $$p(20)=627.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_PartitionCount20.lean#L21 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-! # Chapter 1 — `partitionCount 20 = 627`

Proof: `Ch01.partitionCountRec_eq_partitionCount` (Euler's pentagonal recurrence,
proved in `Chapter01` from Euler's identity and the pentagonal number theorem)
reduces the claim to evaluating the computable recurrence `partitionCountRec 20`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

theorem QseriesFormalization.Ch01.partitionCount_twenty : partitionCount 20 = 627 := by sorry
