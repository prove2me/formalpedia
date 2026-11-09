-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_subset_sum_randomized_time
-- name    : SubsetSumPartialMatch.SubsetSum.subset_sum_randomized_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:42.051895+00:00
-- url     : https://prove2.me/theorems/32694582-5e53-48de-a934-b4750014d83a
-- title:
--   Theorem 4.1 — subset sum in randomized time $O(2^{(1/2-1/450000)n})$
-- statement:
--   Subset sum can be solved by a randomized algorithm in time
--   $$O\bigl(2^{0.49999\overline{7}\,n}\bigr),\qquad0.49999\overline{7}=\frac12-\frac1{450000}.$$
--
--   Explicitly: there is one finite randomized program which, on every signed integer instance $(z,\tau)$ and every random tape, halts and outputs a valid witness or *no solution*; which on instances with a solution outputs *no solution* with probability at most $e^{-n/2}$; and which, for every input-length envelope $B$ of size $2^{o(n)}$, uses at most $C_B\,2^{(1/2-1/450000)n}$ bit operations on every run on an instance with $n\ge N_B$ and input length at most $B(n)$.
--
--   This breaks the $2^{n/2}$ meet-in-the-middle barrier for subset sum.
--
--   Differences from the source:
--   - encoding: $0.49999\overline{7}$ → the exact real $1/2-1/450000$; reason: p. 2 footnote 2 and p. 30 give this value
--   - reading: "randomized algorithm", error unspecified in the statement; p. 14 says the failure probability is exponentially small → no false witness on any tape, *no solution* on a yes-instance with probability at most $e^{-n/2}$, and the time bound on every tape; reason: this is the bound the proof gives, $(1-1/(2n))^{n^2}\le e^{-n/2}$, and it is the stronger reading
--   - generalization: the input length is assumed to be $2^{o(n)}$ bits → halting, validity and the error bound hold on all instances; only the time bound uses the envelope; reason: the source restricts inputs once for the whole paper, and the source case is included
--   - encoding: input length $2^{o(n)}$ bits → every envelope $B$ with $\log_2B(n)/n\to0$ and all instances with $L\le B(n)$; reason: this is the quantified form of the promise; no polynomial bound is imposed
--   - encoding: bit operations → charged cost of the log-cost RAM of the definition `RAM`; reason: the cost is computed from instructions and operand lengths
--   - encoding: an instance of $L$ bits; the output is $c$ or a report that none exists → the words $n,\tau,z_1,\dots,z_n$, one per cell, with $L$ the sum of their bit lengths; the output is the word $0$, or the word $1$ followed by the bits of $c$; reason: machine presentation of the same data; the cells are the delimiters
--   - encoding: $O(2^{en})$ → constants $C>0$ and $N$, chosen after $B$ and before the instance and the tape, with the bound for $n\ge N$; reason: for each $n$ only finitely many instances have $L\le B(n)$, so the threshold changes nothing; the constants depend on the promise, not on the instance
--   - generalization: an algorithm for inputs of length $2^{o(n)}$ → one program, chosen before the envelope $B$, for all envelopes; reason: the source's procedure does not read an envelope; fixing $B$ gives the source case
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 28, Theorem 4.1 (same result as Theorem 1.1, p. 2; proof pp. 28–30)

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Problem

namespace SubsetSumPartialMatch.SubsetSum

/-- Theorem 4.1 (Theorem 1.1). Subset sum can be solved by a randomized algorithm in time
`O(2^{0.49999\overline{7} n})`, that is, with exponent exactly `1/2 - 1/450000`. -/
theorem subset_sum_randomized_time : SolvesSubsetSumIn (1 / 2 - 1 / 450000) := by sorry

end SubsetSumPartialMatch.SubsetSum
