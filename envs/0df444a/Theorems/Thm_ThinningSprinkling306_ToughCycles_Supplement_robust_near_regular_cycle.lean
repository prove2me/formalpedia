-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_Supplement_robust_near_regular_cycle
-- name    : ThinningSprinkling306.ToughCycles.Supplement.robust_near_regular_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:47:48.576199+00:00
-- url     : https://prove2.me/theorems/efcda4da-11d6-4ae4-a25c-e613f6e53166
-- title:
--   Theorem 10.1 — almost spanning cycles from universal sampling robustness
-- statement:
--   All graphs below are finite simple undirected graphs. A family $G_j$ has $n_j$ vertices with $n_j\to\infty$; the index may follow any subsequence of vertex counts. All conclusions are eventual. Sampling retains each vertex independently with probability $p_j\in[0,1]$.
--
--   Let $G_j$ have actual minimum degree $d_j$, maximum degree $\Delta_j$, and $\Delta_j/d_j\to1$, with
--   $$
--   \frac{d_j}{(\log n_j)^3\log\log n_j}\longrightarrow\infty.
--   $$
--   Assume that for every rate family $p_j\in[0,1]$ for which there exists $c>0$ with $p_j\log n_j\ge c$ eventually, one has eventually
--   $$
--   \Pr\!\left(G_j[V_{p_j}]\text{ is }\tfrac12\text{-tough}\right)\ge1-n_j^{-2}.
--   $$
--   Then, for every fixed $\delta>0$, eventually $G_j$ contains a simple cycle of length at least $(1-\delta)n_j$.
--
--   The sampling hypothesis quantifies over every such rate family; its cutoff may depend on the family. It includes $p_j=1$, supplying ambient half-toughness without a separate hypothesis. Together with Lemma 10.2 and the published reservoir lemma, this companion theorem supports Theorems 1.7 and 1.8.
--
--   Differences from the source:
--   - encoding: asymptotics relative to n tending to infinity → arbitrary Fin n_j graph families with real Tendsto limits and eventual conclusions; reason: makes all omega, little-o and eventual quantifiers explicit without fixing a rate or subsequence
--   - encoding: minimum degree d and maximum degree (1+o(1))d → computed minimumDegree and maximumDegree with their ratio tending to one; reason: the extrema are determined by the graph; initial zero degrees have no effect once the divergence hypotheses hold
--   - encoding: whenever p=Omega(1/log n) → for every rate family in [0,1] with some eventually positive lower bound on p_j log n_j; reason: retains the universal robustness premise, its rate-dependent cutoff, exact half-toughness and exact failure n_j^(-2)
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 24, Theorem 10.1 (PDF p. 26); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Supplement_GraphParameters
import Definitions.Def_ThinningSprinkling306_ToughCycles_Sampling
import Definitions.Def_ThinningSprinkling306_ToughCycles_Paths

open Filter

namespace ThinningSprinkling306.ToughCycles.Supplement

/-- Theorem 10.1: robustness is universal over all inverse-logarithmic rate families. -/
theorem robust_near_regular_cycle
    (n : ℕ → ℕ) (G : (j : ℕ) → SimpleGraph (Fin (n j)))
    (hn : Tendsto (fun j => (n j : ℝ)) atTop atTop)
    (hnear : Tendsto (fun j => (maximumDegree (G j) : ℝ) / minimumDegree (G j))
      atTop (nhds 1))
    (hdegree : Tendsto
      (fun j => (minimumDegree (G j) : ℝ) /
        (Real.log (n j) ^ 3 * Real.log (Real.log (n j)))) atTop atTop)
    (hrobust : ∀ p : ℕ → ℝ, (∀ j, p j ∈ Set.Icc (0 : ℝ) 1) →
      (∃ c : ℝ, 0 < c ∧ ∀ᶠ j in atTop, c ≤ p j * Real.log (n j)) →
      ∀ᶠ j in atTop,
        1 - 1 / (n j : ℝ) ^ 2 ≤
          sampleProbability (p j) (fun W => ToughOn (G j) W (1 / 2))) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop, LongCycle (G j) ((1 - δ) * (n j : ℝ)) := by sorry

end ThinningSprinkling306.ToughCycles.Supplement
