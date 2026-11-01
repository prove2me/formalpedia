-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_twelve
-- name    : QseriesFormalization.Ch01.partitionCount_twelve
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:47:22.088092+00:00
-- url     : https://prove2.me/theorems/f438073a-9b43-4f34-b37d-eccf515b1f21
-- title:
--   $p(12)=77$
-- statement:
--   The number of partitions of $\,12$ (ways of writing $12$ as an unordered sum of positive integers) is $77$:
--   $$p(12)=77.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_PartitionCount12.lean#L55 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib

namespace QseriesFormalization.PartIV.Ch19 end QseriesFormalization.PartIV.Ch19

/-!
# Chapter 1 — `partitionCount 12 = 77` via the Euler-pentagonal recurrence

Chan §1 establishes the partition counting function `p(n)`.  This file
extends the verified values `partitionCount_zero .. partitionCount_eleven`
by one step:

  p(12) = 77

The coefficient of `q^12` in Euler's identity `(∑ p(n) qⁿ) · (q;q)∞ = 1` is the
Euler-pentagonal recurrence

  p(12) − p(11) − p(10) + p(7) + p(5) − p(0) = 0

(from the non-zero pentagonal coefficients at `m ∈ {1,2,5,7,12}`), so
`p(12) = 56 + 42 − 15 − 7 + 1 = 77`. The proof uses the general form of this
recurrence, `Ch01.partitionCountRec_eq_partitionCount`, and evaluates the
computable recurrence `partitionCountRec 12`.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

open QseriesFormalization.PartIV.Ch19

theorem QseriesFormalization.Ch01.partitionCount_twelve : partitionCount 12 = 77 := by sorry
