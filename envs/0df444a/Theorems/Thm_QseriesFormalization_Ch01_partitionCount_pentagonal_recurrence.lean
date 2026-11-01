-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_pentagonal_recurrence
-- name    : QseriesFormalization.Ch01.partitionCount_pentagonal_recurrence
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:43:37.75333+00:00
-- url     : https://prove2.me/theorems/d4e4bb9b-af10-4e6f-af96-fecef1547fbc
-- title:
--   Euler's pentagonal recurrence for the partition function
-- statement:
--   For every natural number $n\ge1$, with $p(n)$ the number of partitions of $n$, $\omega(k)=k(3k-1)/2$ and $\omega'(k)=k(3k+1)/2$,
--   $$p(n)=\sum_{j=0}^{n-1}(-1)^j\Big(p\big(n-\omega(j+1)\big)\,[\omega(j+1)\le n]+p\big(n-\omega'(j+1)\big)\,[\omega'(j+1)\le n]\Big),$$
--   where $[\cdot]$ is $1$ if the condition holds and $0$ otherwise (so terms with an index exceeding $n$ are omitted). Equivalently $p(n)=p(n-1)+p(n-2)-p(n-5)-p(n-7)+\cdots$.
--
--   This is the coefficient form of Euler's identity combined with the pentagonal number theorem (Chapter 1) and gives an efficient way to compute $p(n)$.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Declaration from accepted compatibility port b254c67c12688a3437f0c4ed5bdc17b99f52ef3e, port/QseriesFormalization/Chapter01.lean#L194-L228 (file SHA-256 271d8b088bc9a85618efd5c91ca934622b2a64b89ecb54faf07c0c82c14675a1). Related upstream file: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01.lean.

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

theorem QseriesFormalization.Ch01.partitionCount_pentagonal_recurrence {n : Nat} (hn : 1 ≤ n) :
    (partitionCount n : ℤ) =
      ∑ j ∈ Finset.range n, (-1 : ℤ) ^ j *
        ((if pentagonalLower (j + 1) ≤ n then (partitionCount (n - pentagonalLower (j + 1)) : ℤ)
            else 0) +
          (if pentagonalUpper (j + 1) ≤ n then (partitionCount (n - pentagonalUpper (j + 1)) : ℤ)
            else 0)) := by sorry
