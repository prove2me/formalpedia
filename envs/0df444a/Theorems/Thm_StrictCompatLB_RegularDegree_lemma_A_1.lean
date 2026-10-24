-- Prove2me | Theorems.Thm_StrictCompatLB_RegularDegree_lemma_A_1
-- name    : StrictCompatLB.RegularDegree.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:16.934975+00:00
-- url     : https://prove2.me/theorems/5bbf8547-c888-4ff0-bc8e-38a6782a1854
-- title:
--   Lemma A.1 — binomial upper tail: $P(X_N\ge\delta N)\le(a\,p(N)^\delta)^N$ when $p(N)\to0$
-- statement:
--   Let $p(N)\in[0,1]$, $N\ge 1$, be a sequence with $p(N)\to 0$, and let $X_N$ be a Binomial$(N,p(N))$ random variable, so that
--   $$\mathbb P(X_N\ge\delta N)=\sum_{\substack{0\le k\le N\\ k\ge\delta N}}\binom Nk\,p(N)^k\,(1-p(N))^{N-k}.$$
--   Then for every fixed $\delta\in(0,1/2)$ there exist $N_0\ge 1$ and $a>0$ such that for all $N\ge N_0$,
--   $$\mathbb P(X_N\ge\delta N)\;\le\;\big(a\,(p(N))^{\delta}\big)^N .$$
--
--   This tail bound is the tool by which Lemma A.2 controls the number of servers with an atypical number of neighbours in a set of dispatchers. A bound decaying exponentially in $N$ is what makes the union bound over all subsets of dispatchers summable.
--
--   **Formalization Note** The binomial probability is written out as the sum of the binomial point masses; $p(N)^\delta$ is the real power. The bound is as printed in (A.1): the exponent $\delta$ applies to $p(N)$ only, and the whole product is raised to the power $N$.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 30, Lemma A.1, (A.1)

import Mathlib

open Finset Filter Topology

namespace StrictCompatLB.RegularDegree

theorem lemma_A_1 (p : ℕ → ℝ) (hp0 : ∀ N, 0 ≤ p N) (hp1 : ∀ N, p N ≤ 1)
    (hp : Tendsto p atTop (𝓝 0)) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ a : ℝ, 0 < a ∧ ∀ N ≥ N₀,
      ∑ k ∈ (Finset.range (N + 1)).filter (fun k : ℕ => δ * (N : ℝ) ≤ (k : ℝ)),
          (N.choose k : ℝ) * p N ^ k * (1 - p N) ^ (N - k)
        ≤ (a * p N ^ δ) ^ N := by sorry

end StrictCompatLB.RegularDegree
