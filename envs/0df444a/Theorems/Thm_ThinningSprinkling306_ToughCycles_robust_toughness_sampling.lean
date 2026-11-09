-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_robust_toughness_sampling
-- name    : ThinningSprinkling306.ToughCycles.robust_toughness_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:10.517634+00:00
-- url     : https://prove2.me/theorems/7e6469b0-7134-4af2-a70a-5228f9934d47
-- title:
--   Theorem 1.2 — robust vertex sampling of toughness
-- statement:
--   There exist absolute real constants $a,b>0$ such that the following holds for every family of finite simple graphs $G_j$ on $n_j\to\infty$ vertices and real parameters $p_j\in[0,1]$, $t_j$. Suppose $G_j$ is eventually $t_j$-tough and $p_j^2t_j/\log n_j\to+\infty$. Then eventually
--   $$
--   \Pr\big(G_j[V_{p_j}]\text{ is }a p_j^2t_j\text{-tough}\big)
--   \ge1-2^{-b p_j^2t_j}.
--   $$
--   Each $V_{p_j}$ retains the vertices independently with probability $p_j$. The constants are chosen before every family and cannot depend on a graph or a sampling rate. The result retains both absolute constants hidden in the source's $\Omega$ notation and supplies the toughness-sampling target needed by the goal.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → SimpleGraph (Fin n), for arbitrary natural n; reason: every finite graph admits this relabeling, including empty and singleton graphs
--   - encoding: asymptotics as the vertex count n tends to infinity → every sequence of sizes n_j tending to infinity, with real ratios tending to positive infinity and eventual conclusions; reason: arbitrary sizes, subsequences and divergence rates are retained; finite initial terms do not affect the result
--   - encoding: two absolute positive constants in Ω(p²t) → existential real a,b>0 before all graph and parameter families; reason: this expands the source asymptotic constant notation without choosing a numerical value
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 3, Theorem 1.2 (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Sprinkling
open Filter

namespace ThinningSprinkling306.ToughCycles

/-- Theorem 1.2, printed p. 3 (PDF p. 5). Absolute constants precede every family. -/
theorem robust_toughness_sampling :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ (n : ℕ → ℕ) (G : (j : ℕ) → SimpleGraph (Fin (n j))) (p t : ℕ → ℝ),
        Tendsto n atTop atTop →
        (∀ j, p j ∈ Set.Icc (0 : ℝ) 1) →
        (∀ᶠ j in atTop, Tough (G j) (t j)) →
        Tendsto (fun j => p j ^ 2 * t j / Real.log (n j : ℝ)) atTop atTop →
        ∀ᶠ j in atTop,
          1 - (2 : ℝ) ^ (-(b * p j ^ 2 * t j)) ≤
            sampleProbability (p j)
              (fun W => ToughOn (G j) W (a * p j ^ 2 * t j)) := by sorry

end ThinningSprinkling306.ToughCycles
