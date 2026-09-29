-- Prove2me | Theorems.Thm_ProximalBanach_Hybrid_eq32_phi_monotone_step
-- name    : ProximalBanach.Hybrid.eq32_phi_monotone_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:10:06.583262+00:00
-- url     : https://prove2.me/theorems/17ed8765-b1c7-4c31-8fbe-9f690cbee0e0
-- title:
--   (3.2) — φ(x_{n+1}, x_n) + φ(x_n, x_0) ≤ φ(x_{n+1}, x_0) along the algorithm
-- statement:
--   Let $E$ be a reflexive, strictly convex and smooth real Banach space with duality mapping $J$, let $T$ be maximal monotone with $T^{-1}0\neq\emptyset$, let $r_n>0$, and let $(x_n,y_n,v_n)$ be a run of the algorithm (3.1). Then for every $n\ge0$
--   $$\varphi(x_{n+1},x_n)+\varphi(x_n,x_0)\ \le\ \varphi(x_{n+1},x_0).\tag{3.2}$$
--
--   It shows that $\varphi(x_n,x_0)$ is nondecreasing and that the steps $\varphi(x_{n+1},x_n)$ are summable once $\varphi(x_n,x_0)$ is bounded.
--
--   **Formalization Note** On the page (3.2) is the first step of the proof of Theorem 8. It is stated here under the hypotheses of Proposition 7 (reflexive, strictly convex, smooth), which are implied by those of Theorem 8 and are all that the derivation from Propositions 4 and 5 uses; the condition $\liminf r_n>0$ is not needed for this step.
-- source:
--   Kamimura and Takahashi, Strong convergence of a proximal-type algorithm in a Banach space, SIAM J. Optim. 13(3), 2003, pp. 942–943, (3.2) in the proof of Theorem 8

import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Display (3.2) (proof of Theorem 8, p. 943): under the hypotheses of Proposition 7, every
run of (3.1) satisfies `φ(x_{n+1}, x_n) + φ(x_n, x_0) ≤ φ(x_{n+1}, x_0)` for all `n`. -/
theorem eq32_phi_monotone_step [StrictConvexSpace ℝ E] (hR : IsReflexive E)
    (hS : IsSmooth E) (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMaximalMonotone T) (hZ : (zeros T).Nonempty)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) :
    ∀ n : ℕ, phi J (x (n + 1)) (x n) + phi J (x n) (x 0) ≤ phi J (x (n + 1)) (x 0) := by sorry

end ProximalBanach.Hybrid
