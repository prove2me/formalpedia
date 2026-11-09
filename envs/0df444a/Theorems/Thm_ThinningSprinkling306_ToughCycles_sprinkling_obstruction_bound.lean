-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_sprinkling_obstruction_bound
-- name    : ThinningSprinkling306.ToughCycles.sprinkling_obstruction_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:08.352018+00:00
-- url     : https://prove2.me/theorems/cc0f6234-6739-4073-a625-b07f59074ca3
-- title:
--   Lemma 4.2 — strict upper bound on the seeded obstruction
-- statement:
--   There is an absolute $\varepsilon>0$ with the following property. Let $G_j$ be arbitrary finite simple graphs with $n_j\to\infty$, let $p_j\in[0,1]$, and suppose eventually $G_j$ is $t_j$-tough and $p_j^2t_j/\log n_j\to+\infty$. Under the nested conditional-halving law, eventually for every integer $k\ge2$,
--   $$
--   \Pr\big(c_{V_{p_j/4}}(G_j[V_{p_j/2}])\ge k\big)
--   <2^{-4k\varepsilon p_j^2t_j}.
--   $$
--   The same absolute constant serves every family and every $k$. The strict inequality is retained, and the event means at least $k$ seeded components, not exactly $k$ total components. This is the upper obstruction estimate paired with Lemma 4.1.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → SimpleGraph (Fin n), for arbitrary natural n; reason: every finite graph admits this relabeling, including empty and singleton graphs
--   - encoding: asymptotics as the vertex count n tends to infinity → every sequence of sizes n_j tending to infinity, with real ratios tending to positive infinity and eventual conclusions; reason: arbitrary sizes, subsequences and divergence rates are retained; finite initial terms do not affect the result
--   - encoding: p-random subsets and two conditional independent halvings → Mathlib Bernoulli subset measures and their finite product, with V_p=A, V_{p/2}=A intersect B, V_{p/4}=A intersect B intersect C; reason: A has parameter p and B,C independently have parameter 1/2, so this is exactly the joint thinning law
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 9, Lemma 4.2 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Sprinkling
open Filter

namespace ThinningSprinkling306.ToughCycles

/-- Lemma 4.2, printed p. 9 (PDF p. 11). -/
theorem sprinkling_obstruction_bound :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (n : ℕ → ℕ) (G : (j : ℕ) → SimpleGraph (Fin (n j))) (p t : ℕ → ℝ),
        Tendsto n atTop atTop →
        (∀ j, p j ∈ Set.Icc (0 : ℝ) 1) →
        (∀ᶠ j in atTop, Tough (G j) (t j)) →
        Tendsto (fun j => p j ^ 2 * t j / Real.log (n j : ℝ)) atTop atTop →
        ∀ᶠ j in atTop, ∀ k : ℕ, 2 ≤ k →
          nestedProbability (p j)
            (fun _ W A => k ≤ (seededComponents (G j) W A).card) <
              (2 : ℝ) ^ (-4 * (k : ℝ) * ε * p j ^ 2 * t j) := by sorry

end ThinningSprinkling306.ToughCycles
