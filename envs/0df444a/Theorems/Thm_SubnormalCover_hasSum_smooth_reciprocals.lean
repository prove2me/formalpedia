-- Prove2me | Theorems.Thm_SubnormalCover_hasSum_smooth_reciprocals
-- name    : SubnormalCover.hasSum_smooth_reciprocals
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-14T12:45:04.633622+00:00
-- url     : https://prove2.me/theorems/13bfbfea-47aa-446e-9e03-af9e3f6ff441
-- title:
--   Density of a union of arithmetic progressions as an Euler product
-- statement:
--   Let $n_1,\dots,n_k$ be positive integers, let $N$ be any positive common multiple of them, and let $P$ be a finite set of primes containing every prime factor of every $n_i$. Sun's Lemma 3.4 (eq. (3.7)) asserts that the asymptotic density of $\bigcup_{i=1}^{k} n_i\mathbb{Z}$ equals $\left(\prod_{p\in P}\frac{p-1}{p}\right)\sum 1/m$, where $m$ runs over the positive integers divisible by some $n_i$ and having all prime factors in $P$; equivalently, that series converges with sum $d\cdot\prod_{p\in P}\frac{p}{p-1}$, where $d$ is the density. **Formalization note.** Mathlib has no asymptotic-density API, so the density is written in the exact finite form $\bigl|\{0\le x<N : \exists i,\ n_i\mid x\}\bigr|/N$ (independent of which positive common multiple $N$ is chosen), the Euler factor is moved to the right-hand side as $\prod_{p\in P}p/(p-1)$ (well defined because every $p\in P$ is prime, so $p-1\neq 0$), and the conclusion is phrased as an unconditional `HasSum` over the subtype $\{m : 0<m \wedge P(m)\subseteq P \wedge \exists i,\ n_i\mid m\}$, which additionally asserts (unordered) summability.
-- source:
--   Z.-W. Sun, On the Herzog-Schönheim conjecture for uniform covers of groups, J. Algebra 273 (2004) 153-175, https://doi.org/10.1016/S0021-8693(03)00526-X, Lemma 3.4, eq. (3.7)

import Mathlib

namespace SubnormalCover

theorem hasSum_smooth_reciprocals {k : ℕ} (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (N : ℕ) (hN : 0 < N) (hdvd : ∀ i, n i ∣ N)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hsub : ∀ i, (n i).primeFactors ⊆ P) :
    HasSum (fun m : {m : ℕ // 0 < m ∧ m.primeFactors ⊆ P ∧ ∃ i, n i ∣ m} =>
        (1 : ℝ) / ((m : ℕ) : ℝ))
      ((((Finset.range N).filter fun x => ∃ i, n i ∣ x).card : ℝ) / (N : ℝ)
        * ∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1))) := by
  sorry

end SubnormalCover
