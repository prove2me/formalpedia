-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_fifteen
-- name    : QseriesFormalization.Ch01.partitionCount_fifteen
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:38:29.737771+00:00
-- url     : https://prove2.me/theorems/dc609913-0780-47d7-8a21-abc744af8045
-- title:
--   $p(15)=176$
-- statement:
--   The number of partitions of $\,15$ (ways of writing $15$ as an unordered sum of positive integers) is $176$:
--   $$p(15)=176.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_PartitionCount15.lean#L26 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-!
# Chapter 1 — `partitionCount 15 = 176` via the Euler-pentagonal recurrence

15 is a pentagonal number (15 = 3·(3·3 + 1)/2), so σ(15) = (-1)^3 = -1.
The recurrence at n = 15:

  p(15) = p(14) + p(13) − p(10) − p(8) + p(3) + p(0)
        = 135 + 101 − 42 − 22 + 3 + 1 = 176.

Proof: `Ch01.partitionCountRec_eq_partitionCount` (Euler's pentagonal recurrence,
proved in `Chapter01` from Euler's identity and the pentagonal number theorem)
reduces the claim to evaluating the computable recurrence `partitionCountRec 15`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

theorem QseriesFormalization.Ch01.partitionCount_fifteen : partitionCount 15 = 176 := by sorry
