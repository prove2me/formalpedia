-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionSeries_mul_pentagonalSeries
-- name    : QseriesFormalization.Ch01.partitionSeries_mul_pentagonalSeries
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:50:52.770532+00:00
-- url     : https://prove2.me/theorems/d001f850-33a7-4a01-941c-9ef65bf25940
-- title:
--   Euler's identity: $\big(\sum p(n)q^n\big)\prod_{i\ge1}(1-q^i)=1$ in $\mathbb{Z}[[q]]$
-- statement:
--   In the ring of formal power series $\mathbb{Z}[[q]]$, let $P=\sum_{n\ge0}p(n)q^n$ be the generating series of the partition function $p(n)$ (the number of partitions of $n$), and let $E=\prod_{i\ge1}(1-q^i)$ be Mathlib's `pentagonalSeries` (the formal infinite product, whose expansion is given by Euler's pentagonal number theorem). The statement is
--   $$\Big(\sum_{n\ge 0}p(n)\,q^n\Big)\cdot\prod_{i\ge1}(1-q^i)=1 .$$
--   This is Euler's identity $1/\prod(1-q^i)=\sum p(n)q^n$ in Chapter 1, and it is the key input for deducing the pentagonal recurrence for $p(n)$.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Declaration from accepted compatibility port b254c67c12688a3437f0c4ed5bdc17b99f52ef3e, port/QseriesFormalization/Chapter01.lean#L105-L125 (file SHA-256 271d8b088bc9a85618efd5c91ca934622b2a64b89ecb54faf07c0c82c14675a1). Related upstream file: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01.lean.

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

theorem QseriesFormalization.Ch01.partitionSeries_mul_pentagonalSeries :
    (PowerSeries.mk fun n => (partitionCount n : ℤ)) * PowerSeries.pentagonalSeries ℤ = 1 := by sorry
