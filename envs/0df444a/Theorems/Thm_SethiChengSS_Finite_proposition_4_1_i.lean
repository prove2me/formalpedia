-- Prove2me | Theorems.Thm_SethiChengSS_Finite_proposition_4_1_i
-- name    : SethiChengSS.Finite.proposition_4_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:34.57098+00:00
-- url     : https://prove2.me/theorems/0445d6d0-4a0b-4f1e-8fc5-1144b8ed568b
-- title:
--   Proposition 4.1(i), p. 934 — K-convex implies L-convex for L ≥ K; convex functions are K-convex for every K ≥ 0
-- statement:
--   Recall that $g:\mathbb R\to\mathbb R$ is $K$-convex, $K \ge 0$, if $K + g(z+y) \ge g(y) + z\,\frac{g(y)-g(y-b)}{b}$ for all $z \ge 0$, $b > 0$ and $y$ (Definition 4.1).
--
--   1. If $g$ is $K$-convex and $L \ge K$, then $g$ is $L$-convex.
--   2. If $g$ is convex, then $g$ is $0$-convex, and hence $K$-convex for every $K \ge 0$.
--
--   These monotonicity facts let a $K$-convexity bound be relaxed to a larger fixed cost, as in the proof of Theorem 4.1, where (4.1) relaxes $\bar K^i_{n+1}$ to $K^i_n$.
--
--   **Formalization Note** The published `BertsekasDP.kconvex_of_convex` proves the second part. The first part is new here.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 934, Proposition 4.1(i)

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Finite_KConvexity
open MeasureTheory Filter Topology

namespace SethiChengSS.Finite

/-- Proposition 4.1(i) (Sethi–Cheng 1997, p. 934): a `K`-convex function is `L`-convex for every
`L ≥ K`; a convex function is `0`-convex, hence `K`-convex for every `K ≥ 0`. -/
theorem proposition_4_1_i :
    (∀ (K L : ℝ) (g : ℝ → ℝ), 0 ≤ K → K ≤ L → BertsekasKConvex K g → BertsekasKConvex L g) ∧
    (∀ g : ℝ → ℝ, ConvexOn ℝ Set.univ g →
      BertsekasKConvex 0 g ∧ ∀ K : ℝ, 0 ≤ K → BertsekasKConvex K g) := by sorry

end SethiChengSS.Finite
