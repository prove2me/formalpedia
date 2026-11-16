-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_Supplement_expansion_sampling
-- name    : ThinningSprinkling306.ToughCycles.Supplement.expansion_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:45:04.621233+00:00
-- url     : https://prove2.me/theorems/ac7974f4-282d-40da-ae74-0d1c734035dd
-- title:
--   Theorem 1.4 — external expansion under vertex sampling
-- statement:
--   All graphs below are finite simple undirected graphs. A family $G_j$ has $n_j$ vertices with $n_j\to\infty$; the index may follow any subsequence of vertex counts. All conclusions are eventual. Sampling retains each vertex independently with probability $p_j\in[0,1]$.
--
--   There are absolute constants $a,b>0$ with the following property. Let $G_j$ be external vertex $\lambda_j$-expanders with $\lambda_j\le1$, actual minimum degree $d_j$ and maximum degree $\Delta_j$, where $\Delta_j/d_j\to1$. If $p_j^2\lambda_jd_j/\log n_j\to\infty$, then
--   $$
--   \Pr\!\left(G_j[V_{p_j}]\text{ is an }a p_j\lambda_j\text{-expander}\right)\ge1-2^{-b p_j^2\lambda_jd_j}.
--   $$
--   Expansion tests every set of at most half the sampled vertices and counts its external neighbors inside the sample. Both constants precede all graph, expansion and sampling families. No rate of near regularity is prescribed. This is the sampled-expansion companion theorem.
--
--   Differences from the source:
--   - encoding: asymptotics relative to n tending to infinity → arbitrary Fin n_j graph families with real Tendsto limits and eventual conclusions; reason: makes all omega, little-o and eventual quantifiers explicit without fixing a rate or subsequence
--   - encoding: minimum degree d and maximum degree (1+o(1))d → computed minimumDegree and maximumDegree with their ratio tending to one; reason: the extrema are determined by the graph; initial zero degrees have no effect once the divergence hypotheses hold
--   - encoding: Omega constants in the sampling bound → positive real constants quantified before all families, with epsilon fixed first where present; reason: retains uniformity over all graph and sampling instances and the full exponential failure bound
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 3, Theorem 1.4 (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Supplement_GraphParameters
import Definitions.Def_ThinningSprinkling306_ToughCycles_Sampling

open Filter

namespace ThinningSprinkling306.ToughCycles.Supplement

/-- Theorem 1.4: lam and p vary; near regularity has no prescribed rate. -/
theorem expansion_sampling :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    ∀ (n : ℕ → ℕ) (lam p : ℕ → ℝ)
      (G : (j : ℕ) → SimpleGraph (Fin (n j))),
      Tendsto (fun j => (n j : ℝ)) atTop atTop →
      (∀ j, lam j ≤ 1 ∧ ExpandsOn (G j) Finset.univ (lam j)) →
      Tendsto (fun j => (maximumDegree (G j) : ℝ) / minimumDegree (G j))
        atTop (nhds 1) →
      (∀ j, p j ∈ Set.Icc (0 : ℝ) 1) →
      Tendsto (fun j => p j ^ 2 * lam j * minimumDegree (G j) / Real.log (n j))
        atTop atTop →
      ∀ᶠ j in atTop,
        1 - (2 : ℝ) ^ (-b * p j ^ 2 * lam j * minimumDegree (G j)) ≤
          sampleProbability (p j) (fun W => ExpandsOn (G j) W (a * p j * lam j)) := by sorry

end ThinningSprinkling306.ToughCycles.Supplement
