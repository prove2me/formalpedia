-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_final_sprinkling
-- name    : ThinningSprinkling306.ToughCycles.final_sprinkling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:59.692803+00:00
-- url     : https://prove2.me/theorems/cff58ce4-ac75-48e8-beec-957cd758b3c5
-- title:
--   Claim 2 (proof of Lemma 4.2) — final seeded-component bound
-- statement:
--   Let $(G_j)$ be any family of finite simple graphs with $n_j\to\infty$, real probabilities $p_j\in[0,1]$, and eventual toughness $t_j$, such that $p_j^2t_j/\log n_j\to+\infty$. At each index and every $2\le k\le n_j$, use $m=\lfloor kp_j^2t_j/128\rfloor$, $q=16/(kp_jt_j)$, independent $U_0$ of parameter $p_j/4$ and $U_1,\ldots,U_m$ of parameter $q$. A component of $G_j[\bigcup_{i=0}^m U_i]$ is seeded if it meets $U_0$.
--
--   Fix any outcome of these sets satisfying the short-connection event of Claim 1, and independently sample $B$ with parameter $p_j/8$. There is an absolute $c_2>0$, uniform over families, $k$ and the fixed outcome, such that eventually
--   $$
--   \Pr_B\left(c_{U_0}\!\left(G_j\left[\bigcup_{i=0}^m U_i\cup B\right]\right)\le k-1\right)
--   \ge1-\exp(-kc_2p_j^2t_j).
--   $$
--   The bound concerns all seeded components after the fresh sprinkling. Quantifying over each fixed outcome expresses the printed conditioning without dividing by the probability of a null event.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → SimpleGraph (Fin n), for arbitrary natural n; reason: every finite graph admits this relabeling, including empty and singleton graphs
--   - encoding: asymptotics as the vertex count n tends to infinity → every sequence of sizes n_j tending to infinity, with real ratios tending to positive infinity and eventual conclusions; reason: arbitrary sizes, subsequences and divergence rates are retained; finite initial terms do not affect the result
--   - reading: m=kp²t/128 suppresses integer rounding → m=floor(kp²t/128), with q=16/(kpt) unchanged; reason: the integer round count preserves mq≤p/8 and has the same asymptotic scale uniformly for 2≤k≤n
--   - encoding: condition on an outcome satisfying Claim 1 → for every fixed tuple satisfying exactly that short-connection event, take probability only over a fresh independent final set; reason: this expresses the same conditional claim and is meaningful also for an outcome of probability zero
--   - encoding: internally vertex-disjoint paths joining selected components → paths with interiors outside the selected components, pairwise disjoint outside their union; reason: trim connectors at selected-component encounters; distinct induced components have no edges between them, so each connector retains an outside internal vertex and trimming preserves the path count and disjointness
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 10, Claim 2, proof of Lemma 4.2 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Sprinkling
open Filter

namespace ThinningSprinkling306.ToughCycles

/-- Section 4, proof of Lemma 4.2, Claim 2, printed p. 10 (PDF p. 12). -/
theorem final_sprinkling :
    ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ (n : ℕ → ℕ) (G : (j : ℕ) → SimpleGraph (Fin (n j))) (p t : ℕ → ℝ),
        Tendsto n atTop atTop →
        (∀ j, p j ∈ Set.Icc (0 : ℝ) 1) →
        (∀ᶠ j in atTop, Tough (G j) (t j)) →
        Tendsto (fun j => p j ^ 2 * t j / Real.log (n j : ℝ)) atTop atTop →
        ∀ᶠ j in atTop, ∀ k : ℕ, 2 ≤ k → k ≤ n j →
          ∀ U : Fin (roundCount k (p j) (t j) + 1) → Finset (Fin (n j)),
            WellJoined (G j) (sprinklingUnion U) (U 0) k (t j) →
            1 - Real.exp (-(k : ℝ) * c₂ * p j ^ 2 * t j) ≤
              sampleProbability (p j / 8) (fun B =>
                (seededComponents (G j) (sprinklingUnion U ∪ B) (U 0)).card ≤ k - 1) := by sorry

end ThinningSprinkling306.ToughCycles
