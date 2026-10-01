-- Prove2me | Theorems.Thm_ProximalBanach_Hybrid_duality_uniformContinuousOn
-- name    : ProximalBanach.Hybrid.duality_uniformContinuousOn
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:09:37.87224+00:00
-- url     : https://prove2.me/theorems/c918eb45-0e33-45fd-94c7-7252cc0cc7cf
-- title:
--   Property 4 of the duality mapping — on a uniformly smooth space J is uniformly continuous on bounded sets
-- statement:
--   Let $E$ be a uniformly smooth real Banach space and $J:E\to E^*$ its (single-valued) duality mapping. Then $J$ is uniformly norm-to-norm continuous on each bounded subset $B$ of $E$:
--   $$\forall\varepsilon>0\ \exists\delta>0\ \forall x,y\in B:\ \|x-y\|<\delta\ \Rightarrow\ \|Jx-Jy\|_{E^*}<\varepsilon .$$
--
--   In Theorem 8 this turns $x_n-y_n\to0$ into $Jx_n-Jy_n\to0$, hence $v_n\to0$.
--
--   **Formalization Note** $J$ is a function with $Jx\in\{v:\langle x,v\rangle=\|x\|^2=\|v\|^2\}$ for all $x$; the norm on $E^*$ is the operator norm.
-- source:
--   Kamimura and Takahashi, Strong convergence of a proximal-type algorithm in a Banach space, SIAM J. Optim. 13(3), 2003, p. 939, §2, property 4 of the duality mapping

import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- §2, p. 939, property 4 of the duality mapping: if `E` is uniformly smooth, then `J` is
uniformly norm-to-norm continuous on each bounded subset of `E`. -/
theorem duality_uniformContinuousOn (hUS : IsUniformlySmooth E) (J : E → StrongDual ℝ E)
    (hJ : ∀ x, J x ∈ dualityMap x) (B : Set E) (hB : Bornology.IsBounded B) :
    UniformContinuousOn J B := by sorry

end ProximalBanach.Hybrid
