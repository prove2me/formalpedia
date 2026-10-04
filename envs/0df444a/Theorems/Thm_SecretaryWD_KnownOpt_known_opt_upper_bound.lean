-- Prove2me | Theorems.Thm_SecretaryWD_KnownOpt_known_opt_upper_bound
-- name    : SecretaryWD.KnownOpt.known_opt_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:59:12.598771+00:00
-- url     : https://prove2.me/theorems/ba8d9909-7403-4b00-999d-c94e8f51ced2
-- title:
--   Theorem 4.7 (Known-OPT: Upper Bound) — Z ≤ E[OPT] implies E[A] ≥ Z/4
-- statement:
--   Consider the discounted secretary problem: $n\ge1$ elements with values $v(e)\ge0$ arrive in a uniformly random order $\pi$ (element $\pi(t)$ at time $t$), there is a discount $d(t)\ge0$ on each time, and selecting the element arriving at time $t$ earns $d(t)v(\pi(t))$. Let $\mathbf E[\mathrm{OPT}]=\sum_{\pi\in S_n}\frac1{n!}\max_{i}d(i)v(\pi(i))$ be the expected offline optimum.
--
--   For a real $Z$, algorithm $\mathcal A$ picks the first element $e$ seen, say at time $j$, with $v(e)d(j)\ge Z/2$ (and nothing if there is none). If $Z\le\mathbf E[\mathrm{OPT}]$, then
--
--   $$\mathbf E[\mathcal A]\ \ge\ \frac Z4.$$
--
--   With $Z=\mathbf E[\mathrm{OPT}]$ this gives $\mathbf E[\mathrm{OPT}]\le4\,\mathbf E[\mathcal A]$: when the expected optimum is known in advance, a single threshold is 4-competitive, in contrast to the $\Omega(\log n/\log\log n)$ lower bound without that knowledge (Theorem 4.3). This is the paper's Theorem 1.2.
--
--   **Formalization Note** The constant $1/4$ is the paper's. No sign condition is placed on $Z$: for $Z\le0$ the algorithm takes the first element and the bound holds trivially. The comparison is multiplicative, without a quotient, so $\mathbf E[\mathcal A]=0$ creates no loophole.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 7, Theorem 4.7 (proof p. 8); headline p. 2, Theorem 1.2

import Mathlib
import Definitions.Def_SecretaryWD_KnownOpt_Model

namespace SecretaryWD.KnownOpt

theorem known_opt_upper_bound {n : ℕ} [NeZero n] (d v : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hv : ∀ e, 0 ≤ v e) (Z : ℝ) (hZ : Z ≤ expectedOPT d v) :
    Z / 4 ≤ expectedAlg d v Z := by sorry

end SecretaryWD.KnownOpt
