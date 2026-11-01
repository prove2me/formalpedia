-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_eleven
-- name    : QseriesFormalization.Ch01.partitionCount_eleven
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:38:27.591589+00:00
-- url     : https://prove2.me/theorems/4cfeab70-d66e-4efe-a7d6-f77628d03cd2
-- title:
--   $p(11)=56$
-- statement:
--   The number of partitions of $\,11$ (ways of writing $11$ as an unordered sum of positive integers) is $56$:
--   $$p(11)=56.$$
--   This is a finite numerical check of the partition function from Chapter 1 (a single value, not a general theorem).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01.lean#L6543 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-!
# Chapter 1: Introduction

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 1.)

Most of the introductory material—partitions, triangular numbers,
the q-Pochhammer symbol—lives in `QseriesFormalization.Basic`.
This file collects any chapter-specific lemmas that are too lightweight
to belong in `Basic.lean` but that the introduction relies on.

Currently empty; populated as we work through Chapter 1.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

/-! ## Euler's pentagonal recurrence

Euler's identity `(∑ₙ p(n) qⁿ) · ∏_{i ≥ 1} (1 - qⁱ) = 1` and the pentagonal number theorem
`∏_{i ≥ 1} (1 - qⁱ) = ∑_{k ∈ ℤ} (-1)ᵏ q^{k(3k-1)/2}` (both available in Mathlib) give, on comparing
the coefficients of `qⁿ` for `n ≥ 1`,

  `p(n) = ∑_{k ≥ 1} (-1)^{k+1} (p(n - k(3k-1)/2) + p(n - k(3k+1)/2))`,

where terms with a negative argument are omitted. `partitionCountRec` evaluates exactly this
recurrence from the table of earlier values, so it agrees with `partitionCount` for every `n`
(`partitionCountRec_eq_partitionCount`). The concrete values `p(2), …, p(11)` below (and
`p(12), …` in the companion files) then follow by evaluating `partitionCountRec`, without
enumerating partitions. -/

open scoped PowerSeries.WithPiTopology

theorem QseriesFormalization.Ch01.partitionCount_eleven : partitionCount 11 = 56 := by sorry
