-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_Supplement_expander_toughness_sampling
-- name    : ThinningSprinkling306.ToughCycles.Supplement.expander_toughness_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:46:23.89008+00:00
-- url     : https://prove2.me/theorems/767d8592-ea68-4545-9e47-d1971f31919a
-- title:
--   Corollary 8.4 — near-one toughness in expander samples
-- statement:
--   All graphs below are finite simple undirected graphs. A family $G_j$ has $n_j$ vertices with $n_j\to\infty$; the index may follow any subsequence of vertex counts. All conclusions are eventual. Sampling retains each vertex independently with probability $p_j\in[0,1]$.
--
--   For every fixed $\varepsilon>0$ there is $b_\varepsilon>0$, depending only on $\varepsilon$. Let $G_j$ be external vertex $\lambda_j$-expanders with $\lambda_j\le1$, actual minimum degree $d_j$, maximum degree $\Delta_j$ and $\Delta_j/d_j\to1$. For every sampling family with $p_j^2\lambda_jd_j/\log n_j\to\infty$,
--   $$
--   \Pr\!\left(G_j[V_{p_j}]\text{ is }(1-\varepsilon)\text{-tough}\right)\ge1-2^{-b_\varepsilon p_j^2\lambda_jd_j}.
--   $$
--   The bound covers every fixed positive loss, with a constant chosen before every graph family. This is the sampled-toughness bridge explicitly used in the proof of Theorem 1.8.
--
--   Differences from the source:
--   - encoding: asymptotics relative to n tending to infinity → arbitrary Fin n_j graph families with real Tendsto limits and eventual conclusions; reason: makes all omega, little-o and eventual quantifiers explicit without fixing a rate or subsequence
--   - encoding: minimum degree d and maximum degree (1+o(1))d → computed minimumDegree and maximumDegree with their ratio tending to one; reason: the extrema are determined by the graph; initial zero degrees have no effect once the divergence hypotheses hold
--   - encoding: Omega constants in the sampling bound → positive real constants quantified before all families, with epsilon fixed first where present; reason: retains uniformity over all graph and sampling instances and the full exponential failure bound
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 22, Corollary 8.4 (PDF p. 24); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Supplement_GraphParameters
import Definitions.Def_ThinningSprinkling306_ToughCycles_Sampling

open Filter

namespace ThinningSprinkling306.ToughCycles.Supplement

/-- Corollary 8.4: the exponent constant depends only on ε. -/
theorem expander_toughness_sampling (ε : ℝ) (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧
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
          sampleProbability (p j) (fun W => ToughOn (G j) W (1 - ε)) := by sorry

end ThinningSprinkling306.ToughCycles.Supplement
