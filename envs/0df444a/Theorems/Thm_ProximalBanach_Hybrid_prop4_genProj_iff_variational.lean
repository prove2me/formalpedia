-- Prove2me | Theorems.Thm_ProximalBanach_Hybrid_prop4_genProj_iff_variational
-- name    : ProximalBanach.Hybrid.prop4_genProj_iff_variational
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:07:10.083985+00:00
-- url     : https://prove2.me/theorems/0810f5a0-dd3b-4d73-a8ba-baaffab81003
-- title:
--   Proposition 4 — variational characterization of the generalized projection
-- statement:
--   Let $E$ be a smooth real Banach space with duality mapping $J$, let $C\subseteq E$ be convex, let $x\in E$ and $x_0\in C$. Then
--   $$\varphi(x_0,x)=\inf\{\varphi(z,x):z\in C\}\tag{2.4}$$
--   if and only if
--   $$\langle z-x_0,\ Jx_0-Jx\rangle\ \ge\ 0\qquad\text{for all } z\in C.\tag{2.5}$$
--
--   This is the Banach-space analogue of the obtuse-angle characterization of the metric projection in a Hilbert space; the paper uses it to show $T^{-1}0\subseteq W_n$ and $Q_{W_n}x_0=x_n$.
--
--   **Formalization Note** Since $x_0\in C$, (2.4) is stated as $\varphi(x_0,x)\le\varphi(z,x)$ for all $z\in C$. $C$ is not assumed closed or nonempty beyond $x_0\in C$, as on the page.
-- source:
--   Kamimura and Takahashi, Strong convergence of a proximal-type algorithm in a Banach space, SIAM J. Optim. 13(3), 2003, p. 941, Proposition 4, (2.4)–(2.5)

import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Proposition 4 (p. 941): in a smooth Banach space, for a convex `C`, `x ∈ E` and
`x₀ ∈ C`, `φ(x₀, x) = inf {φ(z, x) : z ∈ C}` (2.4) iff `⟨z - x₀, J x₀ - J x⟩ ≥ 0` for all
`z ∈ C` (2.5). -/
theorem prop4_genProj_iff_variational (hS : IsSmooth E) (J : E → StrongDual ℝ E)
    (hJ : ∀ x, J x ∈ dualityMap x) (C : Set E) (hcv : Convex ℝ C) (x x₀ : E)
    (hx₀ : x₀ ∈ C) :
    (∀ z ∈ C, phi J x₀ x ≤ phi J z x) ↔ ∀ z ∈ C, 0 ≤ (J x₀ - J x) (z - x₀) := by sorry

end ProximalBanach.Hybrid
