-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_reduction_to_partial_match
-- name    : SubsetSumPartialMatch.SubsetSum.reduction_to_partial_match
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:36.611637+00:00
-- url     : https://prove2.me/theorems/646550ef-52a5-4340-8e7c-f9e8acda990e
-- title:
--   Theorem 2.2 — reduce subset sum to half-stars partial match
-- statement:
--   Suppose $(l,r)$ is an admissible exponent pair and $l+r\le1/2-2\xi$ for some $\xi>0$. For every $\varepsilon>0$, subset sum has a randomized algorithm in time
--   $$O\bigl(2^{(1/2-\xi/9+\varepsilon)n}\bigr).$$
--
--   Improving the sum $l+r$ below $1/2$ by any positive constant therefore beats $2^{n/2}$ for subset sum. "Randomized algorithm in time" has the meaning of the predicate $\mathrm{Solves}$ of the definition `Problem`.
--
--   Differences from the source:
--   - reading: "randomized algorithm", error unspecified in the statement; p. 14 says the failure probability is exponentially small → no false witness on any tape, *no solution* on a yes-instance with probability at most $e^{-n/2}$, and the time bound on every tape; reason: this is the bound the proof gives, $(1-1/(2n))^{n^2}\le e^{-n/2}$, and it is the stronger reading
--   - generalization: the input length is assumed to be $2^{o(n)}$ bits → halting, validity and the error bound hold on all instances; only the time bound uses the envelope; reason: the source restricts inputs once for the whole paper, and the source case is included
--   - encoding: input length $2^{o(n)}$ bits → every envelope $B$ with $\log_2B(n)/n\to0$ and all instances with $L\le B(n)$; reason: this is the quantified form of the promise; no polynomial bound is imposed
--   - encoding: bit operations → charged cost of the log-cost RAM of the definition `RAM`; reason: the cost is computed from instructions and operand lengths
--   - encoding: $A,B$ are sets; time $O(2^{(l+\varepsilon)n}|A|+2^{(r+\varepsilon)n}|B|)$ → duplicate-free lists in any order; time $C(1+2^{(l+\varepsilon)n}|A|+2^{(r+\varepsilon)n}|B|)$ for $n\ge N$; reason: a set must be presented to a machine; the $1$ is the constant overhead of a run and matters only for $A=B=\emptyset$
--   - encoding: an instance of $L$ bits; the output is $c$ or a report that none exists → the words $n,\tau,z_1,\dots,z_n$, one per cell, with $L$ the sum of their bit lengths; the output is the word $0$, or the word $1$ followed by the bits of $c$; reason: machine presentation of the same data; the cells are the delimiters
--   - encoding: $O(2^{en})$ → constants $C>0$ and $N$, chosen after $B$ and before the instance and the tape, with the bound for $n\ge N$; reason: for each $n$ only finitely many instances have $L\le B(n)$, so the threshold changes nothing; the constants depend on the promise, not on the instance
--   - generalization: an algorithm for inputs of length $2^{o(n)}$ → one program, chosen before the envelope $B$, for all envelopes; reason: the source's procedure does not read an envelope; fixing $B$ gives the source case
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 10, Theorem 2.2

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Problem
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_PartialMatch

namespace SubsetSumPartialMatch.SubsetSum

/-- Theorem 2.2. If `(l, r)` is an admissible exponent pair and `l + r ≤ 1/2 - 2ξ` for some `ξ > 0`,
then for every `ε > 0` subset sum has a randomized algorithm in time `O(2^{(1/2-ξ/9+ε)n})`. -/
theorem reduction_to_partial_match {l r ξ : ℝ} (hadm : AdmissiblePair l r) (hξ : 0 < ξ)
    (hlr : l + r ≤ 1 / 2 - 2 * ξ) {ε : ℝ} (hε : 0 < ε) :
    SolvesSubsetSumIn (1 / 2 - ξ / 9 + ε) := by sorry

end SubsetSumPartialMatch.SubsetSum
