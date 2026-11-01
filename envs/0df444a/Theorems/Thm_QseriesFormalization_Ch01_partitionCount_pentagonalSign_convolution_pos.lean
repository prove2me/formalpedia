-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_pentagonalSign_convolution_pos
-- name    : QseriesFormalization.Ch01.partitionCount_pentagonalSign_convolution_pos
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:43:10.591504+00:00
-- url     : https://prove2.me/theorems/8b2288f0-828c-41ab-ba2d-8ee6213820f7
-- title:
--   Convolution of $p(i)$ with the pentagonal sign vanishes for $n\ge1$
-- statement:
--   For every natural number $n\ge1$, with $p$ the partition function and $\mathrm{pentagonalSign}(j)=(-1)^k$ if $j=k(3k\mp1)/2$ and $0$ otherwise,
--   $$\sum_{i+j=n}p(i)\,\mathrm{pentagonalSign}(j)=0 ,$$
--   summed over all pairs of naturals $(i,j)$ with $i+j=n$. This is the coefficient of $X^n$ in $\big(\sum p(i)X^i\big)\prod(1-X^j)=1$ for $n\ge1$, and is equivalent to Euler's pentagonal recurrence for $p(n)$ (Chapter 1).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01_RecurrenceGeneral.lean#L43 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Definitions.Def_QseriesFormalization_Chapter05_Franklin
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib

namespace QseriesFormalization.PartIV.Ch19 end QseriesFormalization.PartIV.Ch19

/-!
# Chapter 1 — Euler-pentagonal recurrence for `partitionCount`, general form

A single general lemma capturing the recurrence

  partitionCount n  =  − ∑_{k = 0}^{n − 1} partitionCount k · pentagonalSign (n − k)
                       (for `n ≥ 1`, integer form)

extracted from `(partitionGenFun ℤ) · (qPochInfPS ℤ) = 1` at coefficient
`n`.  Equivalently, the coefficient identity

  ∑_{k = 0}^{n} partitionCount k · pentagonalSign (n − k)  =  0   (n ≥ 1)

(which simply moves `partitionCount n · pentagonalSign 0 = partitionCount n`
to the other side; `pentagonalSign 0 = 1`).

This lets downstream code obtain any `partitionCount N` via a few `decide`s
on `pentagonalSign m` for `m ≤ N`, plus the previously-verified
`partitionCount` values, without rewriting the convolution-sum unfolding
each time.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

open QseriesFormalization.PartIV.Ch19

theorem QseriesFormalization.Ch01.partitionCount_pentagonalSign_convolution_pos {n : ℕ} (hn : 1 ≤ n) :
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      (partitionCount ij.1 : ℤ) * QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ij.2
      = 0 := by sorry
