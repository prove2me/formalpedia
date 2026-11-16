-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_Supplement_transitive_toughness_sampling
-- name    : ThinningSprinkling306.ToughCycles.Supplement.transitive_toughness_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:44:27.176465+00:00
-- url     : https://prove2.me/theorems/3cd0633d-1f24-4366-ab0c-6e541dd97baf
-- title:
--   Theorem 1.3 — near-one toughness in transitive samples
-- statement:
--   All graphs below are finite simple undirected graphs. A family $G_j$ has $n_j$ vertices with $n_j\to\infty$; the index may follow any subsequence of vertex counts. All conclusions are eventual. Sampling retains each vertex independently with probability $p_j\in[0,1]$.
--
--   For every fixed $\varepsilon>0$ there is $b_\varepsilon>0$, depending only on $\varepsilon$, such that every family of connected $d_j$-regular vertex-transitive graphs and every sampling family with $p_j^2d_j/\log n_j\to\infty$ satisfy
--   $$
--   \Pr\!\left(G_j[V_{p_j}]\text{ is }(1-\varepsilon)\text{-tough}\right)\ge1-2^{-b_\varepsilon p_j^2d_j}.
--   $$
--   Toughness is the published cut-component predicate: deleting $s$ vertices to leave $r\ge2$ components requires $s\ge(1-\varepsilon)r$. This supplies robust near-one toughness for every fixed positive loss.
--
--   Differences from the source:
--   - encoding: asymptotics relative to n tending to infinity → arbitrary Fin n_j graph families with real Tendsto limits and eventual conclusions; reason: makes all omega, little-o and eventual quantifiers explicit without fixing a rate or subsequence
--   - encoding: Omega constants in the sampling bound → positive real constants quantified before all families, with epsilon fixed first where present; reason: retains uniformity over all graph and sampling instances and the full exponential failure bound
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 3, Theorem 1.3 (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Supplement_GraphParameters
import Definitions.Def_ThinningSprinkling306_ToughCycles_Sampling
import Definitions.Def_DerandSq_IsVertexTransitive

open Filter

namespace ThinningSprinkling306.ToughCycles.Supplement

/-- Theorem 1.3: the exponent constant depends only on the fixed loss ε. -/
theorem transitive_toughness_sampling (ε : ℝ) (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧
    ∀ (n d : ℕ → ℕ) (p : ℕ → ℝ)
      (G : (j : ℕ) → SimpleGraph (Fin (n j))),
      Tendsto (fun j => (n j : ℝ)) atTop atTop →
      (∀ j, (G j).Connected ∧ RegularOn (G j) Finset.univ (d j) ∧
        DerandSq.IsVertexTransitive (G j)) →
      (∀ j, p j ∈ Set.Icc (0 : ℝ) 1) →
      Tendsto (fun j => p j ^ 2 * (d j : ℝ) / Real.log (n j)) atTop atTop →
      ∀ᶠ j in atTop,
        1 - (2 : ℝ) ^ (-b * p j ^ 2 * (d j : ℝ)) ≤
          sampleProbability (p j) (fun W => ToughOn (G j) W (1 - ε)) := by sorry

end ThinningSprinkling306.ToughCycles.Supplement
