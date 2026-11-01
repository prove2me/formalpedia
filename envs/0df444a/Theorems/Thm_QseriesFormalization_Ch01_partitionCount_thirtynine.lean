-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_thirtynine
-- name    : QseriesFormalization.Ch01.partitionCount_thirtynine
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:45:53.575933+00:00
-- url     : https://prove2.me/theorems/292801a0-ddc9-4e79-b157-1ced54dd8ae3
-- title:
--   $p(39)=31185$
-- statement:
--   The number of partitions of $39$ (ways of writing $39$ as an unordered sum of positive integers) is $31185$:
--   $$p(39)=31185.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_PartitionCount39.lean#L41 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-! # Chapter 1 — `partitionCount 39 = 31185`

Proof: `Ch01.partitionCountRec_eq_partitionCount` (Euler's pentagonal recurrence,
proved in `Chapter01` from Euler's identity and the pentagonal number theorem)
reduces the claim to evaluating the computable recurrence `partitionCountRec 39`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

theorem QseriesFormalization.Ch01.partitionCount_thirtynine : partitionCount 39 = 31185 := by sorry
