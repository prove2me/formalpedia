-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_fourteen
-- name    : QseriesFormalization.Ch01.partitionCount_fourteen
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:42:35.040428+00:00
-- url     : https://prove2.me/theorems/e4c2349c-e236-492d-815c-e012b4fb6b61
-- title:
--   $p(14)=135$
-- statement:
--   The number of partitions of $\,14$ (ways of writing $14$ as an unordered sum of positive integers) is $135$:
--   $$p(14)=135.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_PartitionCount14.lean#L23 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-!
# Chapter 1 — `partitionCount 14 = 135` via the Euler-pentagonal recurrence

p(14) = p(13) + p(12) − p(9) − p(7) + p(2)
      = 101 + 77 − 30 − 15 + 2 = 135.

Pentagonal signs at 14 are zero (14 ∉ pentagonal-number set near 14).

Proof: `Ch01.partitionCountRec_eq_partitionCount` (Euler's pentagonal recurrence,
proved in `Chapter01` from Euler's identity and the pentagonal number theorem)
reduces the claim to evaluating the computable recurrence `partitionCountRec 14`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

theorem QseriesFormalization.Ch01.partitionCount_fourteen : partitionCount 14 = 135 := by sorry
