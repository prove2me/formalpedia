-- Prove2me | Theorems.Thm_SecretaryAdvice_SamplesDual_theorem_17
-- name    : SecretaryAdvice.SamplesDual.theorem_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:43:16.165985+00:00
-- url     : https://prove2.me/theorems/1c4f4aa4-4965-4129-8996-99b224e504ec
-- title:
--   Theorem 17, p. 17 — explicit closed form of the greedy dual solution for secretaries with k samples
-- statement:
--   Consider the secretary problem with $n$ secretaries and $k$ samples: the signal of a secretary is $s\in\{0,\dots,k\}$, the number of sample elements smaller than it. Let $u(i,s)$ be the greedy (backward-induction) solution (8) of the dual LP of §5, with coefficients $a(i,s)=\frac{1}{k+1}\prod_{t=1}^{n-1}\frac{s+t}{k+t+1}$ and $c(j,s',i,s)=\frac{1}{s'+1}\prod_{t=1}^{i-1}\frac{s+t}{s'+t+1}$ for $s'\ge s$ (and $0$ for $s'<s$). Then for every signal $s$,
--
--   $$u(n,s)=\frac{1}{k+1}\prod_{t=1}^{n-1}\frac{s+t}{k+t+1},$$
--
--   and for every round $1\le i<n$ and every signal $s$,
--
--   $$u(i,s)=\max\left\{0,\;\frac{1}{k+1}\prod_{t=1}^{i-1}\frac{s+t}{k+t+1}\left(\prod_{t=i}^{n-1}\frac{s+t}{k+t+1}-\frac{\sum_{j=1}^{n-i}\binom{n-i}{j}\frac1j\prod_{\ell=1}^{j}(k-s+\ell)\prod_{\ell=1}^{n-i-j}(s+i-1+\ell)}{\prod_{t=i}^{n-1}(k+t+1)}\right)\right\},$$
--
--   with the convention $\prod_{t=a}^{b}x_t=1$ if $b<a$.
--
--   Since the greedy solution is optimal for the dual (Theorem 16), this gives a non-recursive description of the optimal dual solution, from which the optimal thresholds in signal space can be read off.
--
--   **Formalization Note** Rounds are $1,\dots,n$ as natural numbers, signals are `Fin (k + 1)`, and all arithmetic is in $\mathbb R$. The statement keeps the $\max\{0,\cdot\}$: it is about the greedy recursion (8) as defined, which clips at every round. The paper's proof treats the recursion with the maximum removed (the companion milestone `unclipped_closed_form`); the passage from the un-clipped to the clipped recursion is not argued in the paper and is part of this goal.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 17, Theorem 17

import Mathlib
import Definitions.Def_SecretaryAdvice_SamplesDual_ClosedForm

open Finset

namespace SecretaryAdvice.SamplesDual

/-- Theorem 17, p. 17: the greedy dual solution (8) with the samples coefficients of §5 is
`u(n,s) = 1/(k+1)·∏_{t=1}^{n−1} (s+t)/(k+t+1)` and, for `i < n`,
`u(i,s) = max {0, innerFormula n k i s}`, for every round `1 ≤ i ≤ n` and signal `s ∈ {0,…,k}`. -/
theorem theorem_17 (n k i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (s : Fin (k + 1)) :
    samplesGreedy n k i s = explicitFormula n k i s := by sorry

end SecretaryAdvice.SamplesDual
