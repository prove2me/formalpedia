-- Prove2me | Theorems.Thm_ProximalBanach_Hybrid_prop2_sub_tendsto_zero
-- name    : ProximalBanach.Hybrid.prop2_sub_tendsto_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:06:27.362935+00:00
-- url     : https://prove2.me/theorems/c2c0fda5-1232-4dd8-bb02-744c6d26b1f2
-- title:
--   Proposition 2 — φ(y_n, z_n) → 0 with one sequence bounded implies y_n − z_n → 0
-- statement:
--   Let $E$ be a uniformly convex and smooth real Banach space with duality mapping $J$, and let $\varphi(x,y)=\|x\|^2-2\langle x,Jy\rangle+\|y\|^2$. Let $(y_n)$, $(z_n)$ be sequences in $E$. If $\varphi(y_n,z_n)\to0$ and either $(y_n)$ or $(z_n)$ is bounded, then
--   $$y_n-z_n\to0 \quad\text{in norm}.$$
--
--   This is how the paper converts convergence of $\varphi$ into strong convergence, both for $x_n-y_n\to0$ and for the final step of Theorem 8.
--
--   **Formalization Note** $J$ is a function with $Jx\in\{v:\langle x,v\rangle=\|x\|^2=\|v\|^2\}$ for all $x$. Boundedness is boundedness of the range of the sequence.
-- source:
--   Kamimura and Takahashi, Strong convergence of a proximal-type algorithm in a Banach space, SIAM J. Optim. 13(3), 2003, p. 940, Proposition 2

import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Proposition 2 (p. 940): in a uniformly convex smooth Banach space, if
`φ(y_n, z_n) → 0` and either `{y_n}` or `{z_n}` is bounded, then `y_n - z_n → 0`. -/
theorem prop2_sub_tendsto_zero [UniformConvexSpace E] (hS : IsSmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x) (y z : ℕ → E)
    (hφ : Tendsto (fun n => phi J (y n) (z n)) atTop (𝓝 0))
    (hb : Bornology.IsBounded (Set.range y) ∨ Bornology.IsBounded (Set.range z)) :
    Tendsto (fun n => y n - z n) atTop (𝓝 0) := by sorry

end ProximalBanach.Hybrid
