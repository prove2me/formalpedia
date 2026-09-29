-- Prove2me | Theorems.Thm_ProximalBanach_Hybrid_prop3_genProj_existsUnique
-- name    : ProximalBanach.Hybrid.prop3_genProj_existsUnique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:06:48.214471+00:00
-- url     : https://prove2.me/theorems/bb90fc1a-0e0b-423b-a9ee-89f8b92ab883
-- title:
--   Proposition 3 — existence and uniqueness of the generalized projection Q_C x
-- statement:
--   Let $E$ be a reflexive, strictly convex and smooth real Banach space with duality mapping $J$, let $C\subseteq E$ be nonempty, closed and convex, and let $x\in E$. Then there exists a unique $x_0\in C$ such that
--   $$\varphi(x_0,x)=\inf\{\varphi(z,x): z\in C\}. \tag{2.3}$$
--
--   The point $x_0$ is the generalized projection $Q_Cx$; this result makes $Q_C$ a well-defined map $E\to C$, which the algorithm (3.1) uses at every step.
--
--   **Formalization Note** (2.3) with $x_0\in C$ is stated as "$x_0\in C$ and $\varphi(x_0,x)\le\varphi(z,x)$ for all $z\in C$", which is the same as attaining the infimum. Reflexivity is surjectivity of the canonical map $E\to E^{**}$; strict convexity is Mathlib's `StrictConvexSpace ℝ E`.
-- source:
--   Kamimura and Takahashi, Strong convergence of a proximal-type algorithm in a Banach space, SIAM J. Optim. 13(3), 2003, p. 940, Proposition 3, (2.3)

import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Proposition 3 (p. 940): in a reflexive, strictly convex, smooth Banach space, for a
nonempty closed convex `C` and `x ∈ E` there is a unique `x₀ ∈ C` with
`φ(x₀, x) = inf {φ(z, x) : z ∈ C}` (2.3). -/
theorem prop3_genProj_existsUnique [StrictConvexSpace ℝ E] (hR : IsReflexive E)
    (hS : IsSmooth E) (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (C : Set E) (hne : C.Nonempty) (hcl : IsClosed C) (hcv : Convex ℝ C) (x : E) :
    ∃! z : E, IsGenProj J C x z := by sorry

end ProximalBanach.Hybrid
