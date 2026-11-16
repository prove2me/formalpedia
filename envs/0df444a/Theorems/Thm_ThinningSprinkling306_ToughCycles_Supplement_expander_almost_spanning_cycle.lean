-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_Supplement_expander_almost_spanning_cycle
-- name    : ThinningSprinkling306.ToughCycles.Supplement.expander_almost_spanning_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:46:46.413278+00:00
-- url     : https://prove2.me/theorems/efe8e04d-76fa-46fd-92c7-3754015d97ee
-- title:
--   Theorem 1.8 — almost spanning cycles in nearly regular expanders
-- statement:
--   All graphs below are finite simple undirected graphs. A family $G_j$ has $n_j$ vertices with $n_j\to\infty$; the index may follow any subsequence of vertex counts. All conclusions are eventual. Sampling retains each vertex independently with probability $p_j\in[0,1]$.
--
--   Let $G_j$ be external vertex $\lambda_j$-expanders of actual minimum degree $d_j$ and maximum degree $\Delta_j$, with $\Delta_j/d_j\to1$. Suppose both
--   $$
--   \frac{\lambda_jd_j}{(\log n_j)^3}\longrightarrow\infty,
--   \qquad
--   \frac{d_j}{(\log n_j)^3\log\log n_j}\longrightarrow\infty.
--   $$
--   Then for every fixed $\delta>0$, eventually $G_j$ has a simple cycle of length at least $(1-\delta)n_j$.
--
--   There is no added upper bound on $\lambda_j$. Both degree hypotheses and arbitrary near regularity are retained. The paper invokes Corollary 8.4 and Theorem 10.1 for this companion theorem.
--
--   Differences from the source:
--   - encoding: asymptotics relative to n tending to infinity → arbitrary Fin n_j graph families with real Tendsto limits and eventual conclusions; reason: makes all omega, little-o and eventual quantifiers explicit without fixing a rate or subsequence
--   - encoding: minimum degree d and maximum degree (1+o(1))d → computed minimumDegree and maximumDegree with their ratio tending to one; reason: the extrema are determined by the graph; initial zero degrees have no effect once the divergence hypotheses hold
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 4, Theorem 1.8 (PDF p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Supplement_GraphParameters
import Definitions.Def_ThinningSprinkling306_ToughCycles_Paths

open Filter

namespace ThinningSprinkling306.ToughCycles.Supplement

/-- Theorem 1.8: no upper bound on lam is added; both growth conditions remain. -/
theorem expander_almost_spanning_cycle
    (n : ℕ → ℕ) (lam : ℕ → ℝ) (G : (j : ℕ) → SimpleGraph (Fin (n j)))
    (hn : Tendsto (fun j => (n j : ℝ)) atTop atTop)
    (hexp : ∀ j, ExpandsOn (G j) Finset.univ (lam j))
    (hnear : Tendsto (fun j => (maximumDegree (G j) : ℝ) / minimumDegree (G j))
      atTop (nhds 1))
    (hexpdegree : Tendsto
      (fun j => lam j * minimumDegree (G j) / Real.log (n j) ^ 3) atTop atTop)
    (hdegree : Tendsto
      (fun j => (minimumDegree (G j) : ℝ) /
        (Real.log (n j) ^ 3 * Real.log (Real.log (n j)))) atTop atTop) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop, LongCycle (G j) ((1 - δ) * (n j : ℝ)) := by sorry

end ThinningSprinkling306.ToughCycles.Supplement
