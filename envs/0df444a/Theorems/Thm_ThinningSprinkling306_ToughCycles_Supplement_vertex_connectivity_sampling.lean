-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_Supplement_vertex_connectivity_sampling
-- name    : ThinningSprinkling306.ToughCycles.Supplement.vertex_connectivity_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:43:20.327573+00:00
-- url     : https://prove2.me/theorems/3fc48d25-b34f-440e-b002-09d35c844304
-- title:
--   Theorem 1.1 — sharp vertex-connectivity sampling
-- statement:
--   All graphs below are finite simple undirected graphs. A family $G_j$ has $n_j$ vertices with $n_j\to\infty$; the index may follow any subsequence of vertex counts. All conclusions are eventual. Sampling retains each vertex independently with probability $p_j\in[0,1]$.
--
--   There are absolute constants $a,b>0$ such that the following holds for every family of $k_j$-vertex-connected graphs and every sampling-rate family with $p_j^2k_j/\log n_j\to\infty$:
--   $$
--   \Pr\!\left(\kappa(G_j[V_{p_j}])\ge a p_j^2k_j\right)\ge1-2^{-b p_j^2k_j}.
--   $$
--   Real connectivity thresholds use the ceiling integer and require at least that integer plus one vertices. This retains the full exponential robustness guarantee, including the possibility of tiny samples as failure outcomes.
--
--   Differences from the source:
--   - encoding: asymptotics relative to n tending to infinity → arbitrary Fin n_j graph families with real Tendsto limits and eventual conclusions; reason: makes all omega, little-o and eventual quantifiers explicit without fixing a rate or subsequence
--   - encoding: real-valued connectivity lower bound → published integer vertex connectivity compared in the reals with the cardinality clause; reason: exactly the ceiling-threshold convention, including complete graphs and tiny samples
--   - encoding: Omega constants in the sampling bound → positive real constants quantified before all families, with epsilon fixed first where present; reason: retains uniformity over all graph and sampling instances and the full exponential failure bound
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 2, Theorem 1.1 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Supplement_GraphParameters
import Definitions.Def_ThinningSprinkling306_ToughCycles_Sampling

open Filter

namespace ThinningSprinkling306.ToughCycles.Supplement

/-- Theorem 1.1: both positive constants are absolute, before all families. -/
theorem vertex_connectivity_sampling :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    ∀ (n k : ℕ → ℕ) (p : ℕ → ℝ)
      (G : (j : ℕ) → SimpleGraph (Fin (n j))),
      Tendsto (fun j => (n j : ℝ)) atTop atTop →
      (∀ j, ConnectedAt (G j) Finset.univ (k j : ℝ)) →
      (∀ j, p j ∈ Set.Icc (0 : ℝ) 1) →
      Tendsto (fun j => p j ^ 2 * (k j : ℝ) / Real.log (n j)) atTop atTop →
      ∀ᶠ j in atTop,
        1 - (2 : ℝ) ^ (-b * p j ^ 2 * (k j : ℝ)) ≤
          sampleProbability (p j)
            (fun W => ConnectedAt (G j) W (a * p j ^ 2 * (k j : ℝ))) := by sorry

end ThinningSprinkling306.ToughCycles.Supplement
