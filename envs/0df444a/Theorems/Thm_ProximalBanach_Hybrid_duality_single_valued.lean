-- Prove2me | Theorems.Thm_ProximalBanach_Hybrid_duality_single_valued
-- name    : ProximalBanach.Hybrid.duality_single_valued
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:05:18.22934+00:00
-- url     : https://prove2.me/theorems/d97f1c3c-b81b-4a9e-a04a-e0294a086883
-- title:
--   Property 2 of the duality mapping — on a smooth space J is single valued
-- statement:
--   Let $E$ be a real Banach space and $J:E\to2^{E^*}$ its normalized duality mapping, $Jx=\{v\in E^*:\langle x,v\rangle=\|x\|^2=\|v\|^2\}$. If $E$ is smooth, then $J$ is single valued:
--   $$\text{for every } x\in E,\ Jx \text{ consists of exactly one functional}.$$
--
--   This is what allows the paper to treat $J$ as a map $E\to E^*$ on smooth spaces, and so to define $\varphi$ and the algorithm (3.1).
--
--   **Formalization Note** "Single valued" is stated as unique existence of $v\in Jx$. The existence half holds in every normed space (Hahn–Banach); smoothness is needed for uniqueness.
-- source:
--   Kamimura and Takahashi, Strong convergence of a proximal-type algorithm in a Banach space, SIAM J. Optim. 13(3), 2003, p. 939, §2, property 2 of the duality mapping

import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- §2, p. 939, property 2 of the duality mapping: if `E` is smooth, then `J` is single
valued, i.e. `J x` consists of exactly one functional for every `x`. -/
theorem duality_single_valued (hS : IsSmooth E) (x : E) :
    ∃! v : StrongDual ℝ E, v ∈ dualityMap x := by sorry

end ProximalBanach.Hybrid
