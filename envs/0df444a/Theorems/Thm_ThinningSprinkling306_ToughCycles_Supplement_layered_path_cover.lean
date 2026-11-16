-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_Supplement_layered_path_cover
-- name    : ThinningSprinkling306.ToughCycles.Supplement.layered_path_cover
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:47:13.679977+00:00
-- url     : https://prove2.me/theorems/3f257311-08c9-4950-b3ce-71828c583aa3
-- title:
--   Lemma 10.2 — path coverage through nearly regular layers
-- statement:
--   All graphs below are finite simple undirected graphs. A family $G_j$ has $n_j$ vertices with $n_j\to\infty$; the index may follow any subsequence of vertex counts. All conclusions are eventual. Sampling retains each vertex independently with probability $p_j\in[0,1]$.
--
--   For every graph family, let $W_{j,1},\ldots,W_{j,m_j}$ be a vertex partition with $m_j\ge2$ and $W_{j,1}$ largest. Let $d_j>0$, $0\le\alpha_j\le1/2$, and $\eta_j\ge0$ with $\eta_j\to0$. Suppose weights satisfy $d_j\le w_{j,v}\le(1+\eta_j)d_j$. For each consecutive pair of parts, every vertex on either side has between $(1-\alpha_j)w_{j,v}$ and $(1+\alpha_j)w_{j,v}$ neighbors on the opposite side.
--
--   For every fixed $\delta>0$, eventually there is a collection of vertex-disjoint simple paths, with all endpoints in $W_{j,1}\cup W_{j,m_j}$, whose covered vertex set $S_j$ satisfies
--   $$
--   |S_j|\ge(1-2\alpha_j m_j-\delta)n_j.
--   $$
--   The number of layers and $\alpha_j$ may vary arbitrarily; no assumption $\alpha_jm_j\to0$ is made. Singleton paths and the empty path collection are permitted. This is the path-cover support for Theorem 10.1.
--
--   Differences from the source:
--   - encoding: asymptotics relative to n tending to infinity → arbitrary Fin n_j graph families with real Tendsto limits and eventual conclusions; reason: makes all omega, little-o and eventual quantifiers explicit without fixing a rate or subsequence
--   - encoding: d_v in [d,(1+o(1))d] and coverage (1-2 alpha m-o(1))n → a nonnegative envelope eta_j tending to zero and every fixed positive coverage loss, with Fin m_j indices; reason: the envelope is uniform over vertices and the proof controls the remainder even when m varies; printed W_1 and W_m become indices 0 and m-1
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 25, Lemma 10.2 (PDF p. 27); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Supplement_Layers

open Filter

namespace ThinningSprinkling306.ToughCycles.Supplement

/-- Lemma 10.2: m and α may vary, with no condition on mα. -/
theorem layered_path_cover
    (n m : ℕ → ℕ) (G : (j : ℕ) → SimpleGraph (Fin (n j)))
    (W : (j : ℕ) → Fin (m j) → Finset (Fin (n j)))
    (d α η : ℕ → ℝ) (w : (j : ℕ) → Fin (n j) → ℝ)
    (hn : Tendsto (fun j => (n j : ℝ)) atTop atTop)
    (hm : ∀ j, 2 ≤ m j)
    (hpartition : ∀ j, LayerPartition (W j) ∧ FirstLargest (W j))
    (hd : ∀ j, 0 < d j)
    (hα : ∀ j, α j ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hη : ∀ j, 0 ≤ η j) (hηlim : Tendsto η atTop (nhds 0))
    (hweights : ∀ j v, d j ≤ w j v ∧ w j v ≤ (1 + η j) * d j)
    (hdegrees : ∀ j, ConsecutiveDegrees (G j) (W j) (α j) (w j)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop,
      ∃ S : Finset (Fin (n j)), ∃ F : LinearForest (G j) S,
        F.endpoints ⊆ outerLayers (W j) ∧
        (1 - 2 * α j * (m j : ℝ) - δ) * (n j : ℝ) ≤ (S.card : ℝ) := by sorry

end ThinningSprinkling306.ToughCycles.Supplement
