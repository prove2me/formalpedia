-- Prove2me | Theorems.Thm_ProximalBanach_Hybrid_remark1_zeros_subset
-- name    : ProximalBanach.Hybrid.remark1_zeros_subset
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:09:06.874878+00:00
-- url     : https://prove2.me/theorems/6c9eafad-67b5-4c9f-9243-f0cc26c329b5
-- title:
--   Remark 1 — T⁻¹0 ⊂ H_n ∩ W_n for every n
-- statement:
--   Let $E$ be a reflexive, strictly convex and smooth real Banach space with duality mapping $J$, let $T$ be maximal monotone with $T^{-1}0\neq\emptyset$, let $r_n>0$, and let $(x_n,y_n,v_n)$ be a run of the algorithm (3.1). Then
--   $$T^{-1}0\subseteq H_n\cap W_n\qquad\text{for each } n\ge0.$$
--
--   Consequently the zero set of $T$ is never cut off by the half-spaces, so $\varphi(x_{n+1},x_0)\le\varphi(w,x_0)$ for every $w\in T^{-1}0$.
--
--   **Formalization Note** The remark is stated under the hypotheses of Proposition 7, from whose proof it is drawn, for every run of (3.1).
-- source:
--   Kamimura and Takahashi, Strong convergence of a proximal-type algorithm in a Banach space, SIAM J. Optim. 13(3), 2003, p. 942, Remark 1

import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Remark 1 (p. 942): under the hypotheses of Proposition 7, every run of (3.1) satisfies
`T⁻¹0 ⊂ H_n ∩ W_n` for each `n ≥ 0`. -/
theorem remark1_zeros_subset [StrictConvexSpace ℝ E] (hR : IsReflexive E) (hS : IsSmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMaximalMonotone T) (hZ : (zeros T).Nonempty)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) :
    ∀ n : ℕ, zeros T ⊆ halfH v y n ∩ halfW J x n := by sorry

end ProximalBanach.Hybrid
