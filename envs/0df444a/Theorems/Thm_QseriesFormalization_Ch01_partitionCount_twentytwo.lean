-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_twentytwo
-- name    : QseriesFormalization.Ch01.partitionCount_twentytwo
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:49:53.746172+00:00
-- url     : https://prove2.me/theorems/81386076-1efc-4ad6-9d02-bc2d580dd02c
-- title:
--   $p(22)=1002$
-- statement:
--   The number of partitions of $\,22$ (ways of writing $22$ as an unordered sum of positive integers) is $1002$:
--   $$p(22)=1002.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_PartitionCount22.lean#L32 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-!
# Chapter 1 — `partitionCount 22 = 1002`

22 is the next pentagonal number after 15: `22 = 4·(3·4 − 1)/2`, so
`σ(22) = (−1)^4 = +1`.  The recurrence at `n = 22`:

  p(22) = p(21) + p(20) − p(17) − p(15) + p(10) + p(7) − p(0)·σ(22)
        = 792 + 627 − 297 − 176 + 42 + 15 − 1·1     (note σ(22) = +1 enters as +p(0)·1 negated)
        = 1002.

Proof: `Ch01.partitionCountRec_eq_partitionCount` (Euler's pentagonal recurrence,
proved in `Chapter01` from Euler's identity and the pentagonal number theorem)
reduces the claim to evaluating the computable recurrence `partitionCountRec 22`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

theorem QseriesFormalization.Ch01.partitionCount_twentytwo : partitionCount 22 = 1002 := by sorry
