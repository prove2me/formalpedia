-- Prove2me | Theorems.Thm_RegevLWE_Hyperplane_lemma_3_15
-- name    : RegevLWE.Hyperplane.lemma_3_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:43.006982+00:00
-- url     : https://prove2.me/theorems/17d61472-82d7-4981-9996-95fc304b1806
-- title:
--   Lemma 3.15 — for r ≥ √2·η_ε(L), ε ≤ 1/10, a sample of D_{L,r} avoids any subspace of dimension ≤ n − 1 with probability ≥ 1/10
-- statement:
--   Let $n \ge 1$ and let $L \subset \mathbb{R}^n$ be an $n$-dimensional lattice. Let $0 < \epsilon \le \tfrac1{10}$ and let $r > 0$ satisfy
--   $$r \ge \sqrt2\,\eta_\epsilon(L).$$
--   Then for every linear subspace $H \subseteq \mathbb{R}^n$ of dimension at most $n - 1$, a sample $x$ from the discrete Gaussian $D_{L,r}$ lies outside $H$ with probability at least $\tfrac1{10}$:
--   $$\Pr_{x \sim D_{L,r}}[x \notin H] = \sum_{x \in L,\ x \notin H} \frac{\rho_r(x)}{\rho_r(L)} \;\ge\; \frac{1}{10}.$$
--
--   Above $\sqrt2$ times the smoothing parameter, the discrete Gaussian is not concentrated on any proper subspace. In the paper this is the step that turns a sampler for $D_{L,r}$ into a solver for the shortest independent vectors problem: $n^2$ independent samples contain $n$ linearly independent vectors except with exponentially small probability (Corollary 3.16). The result first appeared, with a proof sketch, in the preliminary version of Micciancio and Regev's work on worst-case to average-case reductions via Gaussian measures.
--
--   **Formalization Note** The hypothesis $n \ge 1$ is added: for $n = 0$ the subtraction $n - 1$ is $0$, the only subspace of dimension $\le 0$ is $\{0\} = \mathbb{R}^0$, and the probability is $0$. The paper's lattice is $n$-dimensional with $n \ge 1$. $\epsilon > 0$ is added because Definition 2.10 defines $\eta_\epsilon$ for $\epsilon > 0$ only (for $\epsilon \le 0$ the Lean infimum is over the empty set, equals $0$, and the hypothesis would be vacuous). $r > 0$ is the reading of a Gaussian width (for $n \ge 1$, $\epsilon > 0$ it already follows from $r \ge \sqrt2\,\eta_\epsilon(L) > 0$). The probability is the real sum of the masses $D_{L,r}(x)$ over the lattice points outside $H$; Gaussian sums over a lattice are summable, so this is the true probability.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:31, Lemma 3.15

import Mathlib
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian

namespace RegevLWE.Hyperplane

theorem lemma_3_15 {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] {ε r : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10)
    (hr : 0 < r) (h : Real.sqrt 2 * RegevLWE.GaussConv.smoothingParam L ε ≤ r)
    (H : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hH : Module.finrank ℝ H ≤ n - 1) :
    (1 / 10 : ℝ) ≤
      ∑' x : {x : L // (x : EuclideanSpace ℝ (Fin n)) ∉ H}, discreteGaussian L r x := by sorry

end RegevLWE.Hyperplane
