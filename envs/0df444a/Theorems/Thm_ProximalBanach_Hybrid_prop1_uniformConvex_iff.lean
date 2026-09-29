-- Prove2me | Theorems.Thm_ProximalBanach_Hybrid_prop1_uniformConvex_iff
-- name    : ProximalBanach.Hybrid.prop1_uniformConvex_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:05:49.705667+00:00
-- url     : https://prove2.me/theorems/d821c7c7-4059-4a7d-a4ab-21aa604a8d1c
-- title:
--   Proposition 1 (Xu) — characterization of uniform convexity by a modulus g
-- statement:
--   Let $s>0$ and let $E$ be a real Banach space with duality mapping $J$. Then $E$ is uniformly convex if and only if there exists a continuous, strictly increasing, convex function $g:[0,\infty)\to[0,\infty)$ with $g(0)=0$ such that
--   $$\|x+y\|^2\ \ge\ \|x\|^2+2\langle y,j\rangle+g(\|y\|)$$
--   for all $x,y$ with $\|x\|\le s$, $\|y\|\le s$ and all $j\in Jx$.
--
--   The function $g$ may depend on $s$. This inequality is the quantitative form of uniform convexity used in Proposition 2.
--
--   **Formalization Note** Uniform convexity is Mathlib's `UniformConvexSpace E` (for every $\varepsilon>0$ there is $\delta>0$ with $\|x+y\|\le2-\delta$ whenever $\|x\|=\|y\|=1$ and $\|x-y\|\ge\varepsilon$), which is equivalent to the sequential definition on p. 939. $g$ is a function $\mathbb R\to\mathbb R$ whose continuity, strict monotonicity and convexity are required on $[0,\infty)$, with $g\ge0$ there. $J$ is the set-valued duality mapping; no smoothness is assumed.
-- source:
--   Kamimura and Takahashi, Strong convergence of a proximal-type algorithm in a Banach space, SIAM J. Optim. 13(3), 2003, p. 940, Proposition 1 (quoted from Xu [13])

import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Proposition 1 (p. 940, Xu): for every `s > 0`, `E` is uniformly convex iff there is a
continuous, strictly increasing, convex `g : [0, ∞) → [0, ∞)` with `g 0 = 0` such that
`‖x + y‖² ≥ ‖x‖² + 2⟨y, j⟩ + g(‖y‖)` for all `‖x‖, ‖y‖ ≤ s` and `j ∈ J x`. -/
theorem prop1_uniformConvex_iff (s : ℝ) (hs : 0 < s) :
    UniformConvexSpace E ↔
      ∃ g : ℝ → ℝ, ContinuousOn g (Set.Ici 0) ∧ StrictMonoOn g (Set.Ici 0) ∧
        ConvexOn ℝ (Set.Ici 0) g ∧ g 0 = 0 ∧ (∀ t : ℝ, 0 ≤ t → 0 ≤ g t) ∧
        ∀ x y : E, ‖x‖ ≤ s → ‖y‖ ≤ s → ∀ j ∈ dualityMap x,
          ‖x‖ ^ 2 + 2 * j y + g ‖y‖ ≤ ‖x + y‖ ^ 2 := by sorry

end ProximalBanach.Hybrid
