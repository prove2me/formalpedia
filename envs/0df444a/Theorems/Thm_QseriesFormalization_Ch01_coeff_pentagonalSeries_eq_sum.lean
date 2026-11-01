-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_coeff_pentagonalSeries_eq_sum
-- name    : QseriesFormalization.Ch01.coeff_pentagonalSeries_eq_sum
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:37:12.935385+00:00
-- url     : https://prove2.me/theorems/7482b38d-af5b-4b0e-be6e-aa754faa5eca
-- title:
--   Coefficients of $\prod(1-q^i)$ as a finite signed count of pentagonal numbers
-- statement:
--   Let $E=\prod_{i\ge1}(1-q^i)\in\mathbb{Z}[[q]]$ (Mathlib's `pentagonalSeries`), and let $\omega(k)=k(3k-1)/2$ and $\omega'(k)=k(3k+1)/2$ denote the lower and upper generalized pentagonal numbers. For natural numbers $k\le m$, the coefficient of $q^k$ in $E$ is
--   $$[q^k]E=\delta_{k,0}+\sum_{j=0}^{m-1}(-1)^{j+1}\big(\delta_{k,\omega(j+1)}+\delta_{k,\omega'(j+1)}\big),$$
--   where $\delta_{a,b}$ is $1$ if $a=b$ and $0$ otherwise.
--
--   This is a finite reformulation of the pentagonal number theorem, used in Chapter 1 to derive Euler's recurrence for $p(n)$.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Declaration from accepted compatibility port b254c67c12688a3437f0c4ed5bdc17b99f52ef3e, port/QseriesFormalization/Chapter01.lean#L127-L192 (file SHA-256 271d8b088bc9a85618efd5c91ca934622b2a64b89ecb54faf07c0c82c14675a1). Related upstream file: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01.lean.

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

theorem QseriesFormalization.Ch01.coeff_pentagonalSeries_eq_sum {m k : Nat} (hk : k ≤ m) :
    PowerSeries.coeff k (PowerSeries.pentagonalSeries ℤ) =
      (if k = 0 then 1 else 0) +
      ∑ j ∈ Finset.range m, (-1 : ℤ) ^ (j + 1) *
        ((if k = pentagonalLower (j + 1) then 1 else 0) +
          (if k = pentagonalUpper (j + 1) then 1 else 0)) := by sorry
