-- Prove2me | Theorems.Thm_SteuerChoo_Discrete_theorem_3_4
-- name    : SteuerChoo.Discrete.theorem_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:47:42.339651+00:00
-- url     : https://prove2.me/theorems/e9273b2c-89fb-4f12-ae4d-0524a2c080c1
-- title:
--   Theorem 3.4 — zᵖ ∈ N uniquely minimizes the augmented program with weights λᵖ and ρ_p
-- statement:
--   Let $k \ge 1$, let $Z \subset \mathbb R^k$ be finite with nondominated set $N$, let $z^*$ be an ideal criterion vector for $Z$, and let $z^p \in N$. With the weights $\lambda^p$ of (b) and the coefficient $\rho_p$ of (3.6), $z^p$ uniquely minimizes the augmented weighted Tchebycheff program
--   $$\min\{\alpha + \rho_p\, e^{\mathsf T}(z^* - z)\} \quad \text{s.t.} \quad \alpha \ge \lambda^p_i(z^*_i - z_i),\ 1 \le i \le k,\quad z \in Z, \tag{3.5}$$
--   that is, for every $z^q \in Z$ with $z^q \ne z^p$,
--   $$\max_i \lambda^p_i(z^*_i - z^p_i) + \rho_p\, e^{\mathsf T}(z^* - z^p) \;<\; \max_i \lambda^p_i(z^*_i - z^q_i) + \rho_p\, e^{\mathsf T}(z^* - z^q).$$
--
--   Every nondominated criterion vector is therefore the unique optimum of an explicitly constructed augmented weighted Tchebycheff program, so it is computed even by a solver that stops at the first optimal solution it finds.
--
--   **Formalization Note** $S$, $f$ and $\alpha$ are eliminated: the objective value of (3.5) at $z$ with minimal $\alpha$ is $\max_i \lambda^p_i(z^*_i - z_i) + \rho_p e^{\mathsf T}(z^*-z)$. The index sets $I_Z$, $I_N$ of the paper only enumerate $Z$ and $N$. The ideal-vector hypothesis is the section's standing assumption on $z^*$. The empty-minimum convention for $\rho_p$ is the one of the definition ($\rho_p = 1$).
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983) 326–344, https://doi.org/10.1007/BF02591870, p. 332, Theorem 3.4, program (3.5), eq. (3.6)

import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

/-- **Theorem 3.4** (Steuer–Choo 1983, p. 332): let `Z` be finite and `zᵖ ∈ N`. Then `zᵖ` uniquely
minimizes the augmented weighted Tchebycheff program (3.5) with the weights `λᵖ` of (b) and `ρ_p` of
(3.6): every other `z^q ∈ Z` has a strictly larger objective value. `z*` is an ideal criterion
vector. -/
theorem theorem_3_4 {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z) :
    ∀ zq ∈ Z, zq ≠ zp →
      augTcheb (lamP zstar zp) (rhoP Z zstar zp) zstar zp <
        augTcheb (lamP zstar zp) (rhoP Z zstar zp) zstar zq := by sorry

end SteuerChoo.Discrete
