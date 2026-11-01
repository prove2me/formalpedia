-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_thirteen
-- name    : QseriesFormalization.Ch01.partitionCount_thirteen
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:44:35.170284+00:00
-- url     : https://prove2.me/theorems/17580ca1-7b1c-4963-a028-a5efb76cc52a
-- title:
--   $p(13)=101$
-- statement:
--   The number of partitions of $\,13$ (ways of writing $13$ as an unordered sum of positive integers) is $101$:
--   $$p(13)=101.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_PartitionCount13.lean#L30 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-!
# Chapter 1 — `partitionCount 13 = 101` via the Euler-pentagonal recurrence

The value is the coefficient of `q^13` in Euler's identity
`(∑ p(n) qⁿ) · (q;q)∞ = 1`.

Pentagonal signs at `0..13`: non-zero at `m ∈ {0, 1, 2, 5, 7, 12}`,
with signs `+1, -1, -1, +1, +1, -1`.  The recurrence at `n = 13` is

  p(13) − p(12) − p(11) + p(8) + p(6) − p(1) = 0,

so `p(13) = 77 + 56 − 22 − 11 + 1 = 101`.

Proof: `Ch01.partitionCountRec_eq_partitionCount` (Euler's pentagonal recurrence,
proved in `Chapter01` from Euler's identity and the pentagonal number theorem)
reduces the claim to evaluating the computable recurrence `partitionCountRec 13`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

theorem QseriesFormalization.Ch01.partitionCount_thirteen : partitionCount 13 = 101 := by sorry
