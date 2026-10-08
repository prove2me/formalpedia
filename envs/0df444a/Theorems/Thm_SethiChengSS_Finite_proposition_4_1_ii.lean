-- Prove2me | Theorems.Thm_SethiChengSS_Finite_proposition_4_1_ii
-- name    : SethiChengSS.Finite.proposition_4_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:52.451854+00:00
-- url     : https://prove2.me/theorems/8a2636d1-9420-4bb7-ba6d-d8303497afc1
-- title:
--   Proposition 4.1(ii), p. 934 — for α, β ≥ 0, αg₁ + βg₂ is (αK + βL)-convex
-- statement:
--   Let $K, L \ge 0$, let $g_1$ be $K$-convex and $g_2$ be $L$-convex. Then for all $\alpha, \beta \ge 0$,
--   $$\alpha g_1 + \beta g_2 \ \text{is}\ (\alpha K + \beta L)\text{-convex}.$$
--
--   In the proof of Theorem 4.1 this carries $K$-convexity through the weighted sum $\sum_j p_{ij}(\cdot)$ in (3.1) and through the addition of the linear term $c^i_n y$.
--
--   **Formalization Note** The published `BertsekasDP.kconvex_combination` requires $\alpha, \beta > 0$. The paper allows zero coefficients, which matter here because transition probabilities may vanish.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 934, Proposition 4.1(ii)

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Finite_KConvexity
open MeasureTheory Filter Topology

namespace SethiChengSS.Finite

/-- Proposition 4.1(ii) (Sethi–Cheng 1997, p. 934): if `g₁` is `K`-convex and `g₂` is
`L`-convex, then for `α, β ≥ 0` the function `α g₁ + β g₂` is `(αK + βL)`-convex. -/
theorem proposition_4_1_ii (K L α β : ℝ) (g₁ g₂ : ℝ → ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (h₁ : BertsekasKConvex K g₁) (h₂ : BertsekasKConvex L g₂) :
    BertsekasKConvex (α * K + β * L) (fun x => α * g₁ x + β * g₂ x) := by sorry

end SethiChengSS.Finite
