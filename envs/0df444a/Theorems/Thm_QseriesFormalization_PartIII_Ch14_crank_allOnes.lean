-- Prove2me | Theorems.Thm_QseriesFormalization_PartIII_Ch14_crank_allOnes
-- name    : QseriesFormalization.PartIII.Ch14.crank_allOnes
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:15:06.267685+00:00
-- url     : https://prove2.me/theorems/c867c52a-0422-4947-8c8c-1ac0b96f83d3
-- title:
--   The all-ones partition of $n$ has crank $-n$ ($n\ge1$)
-- statement:
--   For every natural number $n\ge1$, the partition of $n$ consisting of $n$ parts equal to $1$ has crank $-n$. Recall the Andrews-Garvan crank of a partition $\lambda$: if $1$ is not a part, $c(\lambda)$ is the largest part; if $1$ occurs $\omega$ times, $c(\lambda)=\mu-\omega$ where $\mu$ is the number of parts strictly larger than $\omega$. Here $\omega=n$ and no part exceeds $n$ in the sense $\mu=0$, so $c=0-n=-n$. This is a basic example computation in Chapter 14.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 14. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter14.lean#L334-L370

import Definitions.Def_QseriesFormalization_Chapter14
import Mathlib

/-!
# Chapter 14 — Dyson-Garvan crank

⚠️  **AUX CHAPTER — chapter-main result OPEN**.

Per `PLAYBOOK_AUDIT.md` (2026-05-22): this file contains the formal
definition of the crank statistic (`crank`, `crankOnes`, `crankMu`,
`crankLargest`) and the trivial-shape calculations:

  • `crank_singleton`  : the partition `[n]` has crank `n` (n ≥ 2)
  • `crank_allOnes`    : the partition `[1,1,…,1]` of `n` has crank `-n` (n ≥ 1)

These give two of the five mod-5 residue classes for partitions of 4
(cranks 4 ≡ 4 and -4 ≡ 1 mod 5).  The truncations
`crankGenNumeratorTrunc_N`, `crankGenDenominatorTrunc_N`, etc. are
mechanical scaffold.

**Chan's Ch 14 main result — the Dyson-Garvan theorem that the crank
distributes evenly mod 5 / mod 7 / mod 11 over partitions of `5n+4` /
`7n+5` / `11n+6` respectively, thereby explaining the Ramanujan
congruences combinatorially — is NOT formalized here.**  Even the n=4
special case (`crankDistMod5OfFour` hits all 5 residues mod 5) is only
asserted at the level of definition, not proved.
-/

open QseriesFormalization
open QseriesFormalization.PartIII
open QseriesFormalization.PartIII.Ch14

variable {R : Type*} [Field R]

/-! ### Crank statistic on partitions (Andrews-Garvan 1988)

The crank `c(λ)` of a partition `λ` is defined as:
- If `1 ∉ parts(λ)`: `c(λ) = largest part of λ`.
- If `1 ∈ parts(λ)`: let `ω(λ) = #{occurrences of 1 in λ}`, and
  `μ(λ) = #{parts of λ strictly greater than ω(λ)}`. Then `c(λ) = μ(λ) - ω(λ)`.

Andrews and Garvan showed (1988) that the crank refines the partition function
in such a way that the residue classes modulo 5, 7, 11 explain the
Ramanujan congruences combinatorially.

We work with `Nat.Partition n` from Mathlib (parts is a `Multiset ℕ`). -/

open Nat

theorem QseriesFormalization.PartIII.Ch14.crank_allOnes (n : Nat) (hn : 1 ≤ n) :
    let p : Nat.Partition n := {
      parts := Multiset.replicate n 1
      parts_pos := by
        intro a ha; rw [Multiset.mem_replicate] at ha; omega
      parts_sum := by
        rw [Multiset.sum_replicate]; simp }
    (crank p : Int) = -n := by sorry
