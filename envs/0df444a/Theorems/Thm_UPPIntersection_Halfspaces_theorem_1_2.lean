-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_theorem_1_2
-- name    : UPPIntersection.Halfspaces.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:28:05.495146+00:00
-- url     : https://prove2.me/theorems/2c3b6407-925e-4332-aed6-61bb702144cd
-- title:
--   Theorem 1.2 — $U(HS_{M,d})=O(\log d)$ while $U(HS_{M,d}\wedge HS_{M,d})=\Omega(d)$ for $M\ge2^{Cd}$
-- statement:
--   For natural numbers $M,d\ge1$ let $HS_{M,d}:\{-M,\dots,M\}^d\times\{-M,\dots,M\}^d\to\{-1,1\}$, $HS_{M,d}(a,b)=\operatorname{sgn}(\langle a,b\rangle-1/2)$, be the bounded integer halfspace problem, and let $HS_{M,d}\wedge HS_{M,d}$ be its disjoint conjunction: Alice holds $(a_1,a_2)$, Bob holds $(b_1,b_2)$, and the value is $-1$ ("true") exactly when $HS_{M,d}(a_1,b_1)=HS_{M,d}(a_2,b_2)=-1$. Let $U$ denote unbounded-error communication complexity (private coins, success probability strictly greater than $1/2$ on every input). Then:
--
--   1. there are constants $A,B$ such that for all $M,d\ge1$,
--   $$U(HS_{M,d})\le A\log_2d+B ;$$
--   2. there are constants $C>0$, $c>0$ and $d_0$ such that for all $d\ge d_0$ and all $M\ge2^{Cd}$,
--   $$U(HS_{M,d}\wedge HS_{M,d})\ge c\,d ;$$
--   3. each player's input consists of $d$ coordinates, each one of $2M+1$ values, so the input length is $n=d\,\lceil\log_2(2M+1)\rceil$.
--
--   Taking $M=2^{\Theta(d)}$ gives $n=\Theta(d^2)$, hence an explicit family with $U(F)=O(\log n)$ but $U(F\wedge F)=\Omega(\sqrt n)$: the class $\mathrm{UPP}^{cc}$ is not closed under intersection.
--
--   Differences from the source:
--   - encoding: sign values in {−1, 1}, with −1 meaning logical true → Bool entries with true standing for +1 (as in the published SignRankMargin sign-rank definition); reason: a relabelling of the two values; the signed AND (−1 iff both are −1) becomes Boolean OR of the stored bits, and sign representation becomes A·R > 0 entrywise
--   - encoding: two-party protocols in which both players have an unlimited sequence of private random bits → deterministic protocol trees (published DetCCHard.Protocol) over (input, private tape) pairs, tape = an infinite sequence of independent fair bits (product measure), every bit function measurable in the speaker's tape; cost = tree depth; U = least cost of a protocol that is correct on each input with probability > 1/2; reason: this is the operational model of the source; measurability is what makes the success probability of a protocol defined at all
--   - reading: the protocol's output (the source does not say which party announces it) → the output is the label of the leaf reached, i.e. it is determined by the transcript; reason: the standard convention; any other convention changes U by at most one bit, which every statement here absorbs in its additive constant
--   - reading: for all M, d, U(HS_{M,d}) = O(log d) → ∃ A B, ∀ M d ≥ 1, U(HS_{M,d}) ≤ A log₂ d + B; reason: one pair of constants uniform in M and d; the additive B gives the bound content at d = 1, where log d = 0
--   - reading: there is a constant c such that if M ≥ 2^{cd} then U(HS ∧ HS) = Ω(d) → ∃ C > 0 ∃ c > 0 ∃ d₀, ∀ d ≥ d₀, ∀ M ≥ 2^{Cd}, U(HS_{M,d} ∧ HS_{M,d}) ≥ c d; reason: the threshold exponent (the source's c) is named C here; the Ω-constant and d₀ are quantified before d and M, uniformly in every M above the threshold
--   - reading: "Note that the input length of the problem is n = d·⌈log(2M + 1)⌉" → the grid {−M,…,M}^d has (2M + 1)^d elements; reason: the note records that each of the d coordinates takes one of 2M + 1 values, i.e. ⌈log₂(2M + 1)⌉ bits; the cardinality identity is its mathematical content
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 3, Theorem 1.2 (restatement of Theorem 7.1, p. 29) with Definition 1.1; PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Communication
import Definitions.Def_UPPIntersection_Halfspaces_SignMatrices

namespace UPPIntersection.Halfspaces

theorem theorem_1_2 :
    (∃ A B : ℝ, ∀ M d : ℕ, 0 < M → 0 < d →
      (U (HS M d) : ℝ) ≤ A * Real.logb 2 d + B) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ M : ℕ,
      (2 : ℝ) ^ (C * d) ≤ M → c * d ≤ (U (andSquare (HS M d)) : ℝ)) ∧
    (∀ M d : ℕ, Fintype.card (Grid M d) = (2 * M + 1) ^ d) := by sorry

end UPPIntersection.Halfspaces
