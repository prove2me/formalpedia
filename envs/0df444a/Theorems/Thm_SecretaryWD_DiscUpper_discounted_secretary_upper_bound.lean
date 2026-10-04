-- Prove2me | Theorems.Thm_SecretaryWD_DiscUpper_discounted_secretary_upper_bound
-- name    : SecretaryWD.DiscUpper.discounted_secretary_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:18:12.253133+00:00
-- url     : https://prove2.me/theorems/19765a92-0a6a-4608-862f-17d7605647dd
-- title:
--   Theorem 4.4 — $\mathbb E[\mathsf{OPT}] \le 4e\,(3\lceil\log_2 n\rceil+2)\,\mathbb E[\mathcal A]$ for the discounted secretary problem
-- statement:
--   Consider the discounted secretary problem with $n\ge1$ elements of values $v(e)\ge0$, arriving in a uniformly random order $\pi$, and a discount function $d(t)\ge0$ on the times, known to the algorithm; selecting the element arriving at time $t$ earns $d(t)\,v(\pi(t))$. Let $\mathcal A$ be the algorithm that chooses a discount class $c\in\{1,\dots,M\}$, $M=3\lceil\log_2 n\rceil+2$, uniformly at random and runs the classical secretary rule on the arrivals at the times $P_c=\{i: d(i)\in(2^{-c}d_{\max},2^{-(c-1)}d_{\max}]\}$. Then
--   $$\mathbb E_\pi\Bigl[\max_t d(t)\,v(\pi(t))\Bigr]\;\le\;4e\,\bigl(3\lceil\log_2 n\rceil+2\bigr)\;\mathbb E[\mathcal A].$$
--   In particular $\mathcal A$ is $O(\log n)$-competitive.
--
--   This is the logarithmic upper bound for the discounted secretary problem with an arbitrary discount function, which together with the paper's $\Omega(\log n/\log\log n)$ lower bound determines the competitive ratio up to a $\log\log n$ factor.
--
--   **Formalization Note.** The paper states $\mathbb E[\mathsf{OPT}]/\mathbb E[\mathcal A]\le O(\log n)$. The statement is multiplicative (no division by $\mathbb E[\mathcal A]$) and the constant is the explicit one the proof yields: $2$ from the top-classes estimate, $2e$ from the per-class classical rule, $M$ from the uniform choice of class. Both expectations are exact finite averages over the $n!$ orders (and over $c$). The comparisons use the tie-break order (larger value first, smaller index on equal values); no distinctness of values is assumed.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 7, Theorem 4.4

import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_Algorithm

namespace SecretaryWD.DiscUpper
theorem discounted_secretary_upper_bound (n : ℕ) (hn : 1 ≤ n) (d v : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hv : ∀ e, 0 ≤ v e) :
    expectedOpt d v ≤ 4 * Real.exp 1 * (classCount n : ℝ) * algorithmValue d v := by sorry
end SecretaryWD.DiscUpper
