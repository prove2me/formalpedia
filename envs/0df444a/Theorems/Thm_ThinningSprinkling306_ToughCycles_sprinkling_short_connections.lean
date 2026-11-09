-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_sprinkling_short_connections
-- name    : ThinningSprinkling306.ToughCycles.sprinkling_short_connections
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:25.700215+00:00
-- url     : https://prove2.me/theorems/c2bc058f-161a-46f9-b686-7c6a0c6c6524
-- title:
--   Claim 1 (proof of Lemma 4.2) — many short connections
-- statement:
--   Let $(G_j)$ be any family of finite simple graphs with $n_j\to\infty$, real probabilities $p_j\in[0,1]$, and eventual toughness $t_j$, such that $p_j^2t_j/\log n_j\to+\infty$. At each index and every $2\le k\le n_j$, use $m=\lfloor kp_j^2t_j/128\rfloor$, $q=16/(kp_jt_j)$, independent $U_0$ of parameter $p_j/4$ and $U_1,\ldots,U_m$ of parameter $q$. A component of $G_j[\bigcup_{i=0}^m U_i]$ is seeded if it meets $U_0$.
--
--   There is an absolute $c_1>0$, independent of the entire family and of $k$, such that eventually, simultaneously for all these $k$,
--   $$
--   \Pr\left(\text{every collection of }k\text{ distinct seeded components admits at least }kt_j/4\text{ connecting paths of length at most }3\right)
--   \ge1-\exp(-kc_1p_j^2t_j).
--   $$
--   The paths join two distinct selected components, have interiors outside their union, and intersect only within that union. Component endpoints may be shared. This identifies the precise short-connection event used by the next conditional statement.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → SimpleGraph (Fin n), for arbitrary natural n; reason: every finite graph admits this relabeling, including empty and singleton graphs
--   - encoding: asymptotics as the vertex count n tends to infinity → every sequence of sizes n_j tending to infinity, with real ratios tending to positive infinity and eventual conclusions; reason: arbitrary sizes, subsequences and divergence rates are retained; finite initial terms do not affect the result
--   - reading: m=kp²t/128 suppresses integer rounding → m=floor(kp²t/128), with q=16/(kpt) unchanged; reason: the integer round count preserves mq≤p/8 and has the same asymptotic scale uniformly for 2≤k≤n
--   - encoding: at least a displayed real number of paths → a natural family size r satisfying the same real lower bound; reason: this is the ceiling interpretation and preserves the exact displayed constant
--   - encoding: internally vertex-disjoint paths joining selected components → paths with interiors outside the selected components, pairwise disjoint outside their union; reason: trim connectors at selected-component encounters; distinct induced components have no edges between them, so each connector retains an outside internal vertex and trimming preserves the path count and disjointness
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 9, Claim 1, proof of Lemma 4.2 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Sprinkling
open Filter

namespace ThinningSprinkling306.ToughCycles

/-- Section 4, proof of Lemma 4.2, Claim 1, printed p. 9 (PDF p. 11). -/
theorem sprinkling_short_connections :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (n : ℕ → ℕ) (G : (j : ℕ) → SimpleGraph (Fin (n j))) (p t : ℕ → ℝ),
        Tendsto n atTop atTop →
        (∀ j, p j ∈ Set.Icc (0 : ℝ) 1) →
        (∀ᶠ j in atTop, Tough (G j) (t j)) →
        Tendsto (fun j => p j ^ 2 * t j / Real.log (n j : ℝ)) atTop atTop →
        ∀ᶠ j in atTop, ∀ k : ℕ, 2 ≤ k → k ≤ n j →
          1 - Real.exp (-(k : ℝ) * c₁ * p j ^ 2 * t j) ≤
            sprinklingProbability k (p j) (t j)
              (fun U => WellJoined (G j) (sprinklingUnion U) (U 0) k (t j)) := by sorry

end ThinningSprinkling306.ToughCycles
