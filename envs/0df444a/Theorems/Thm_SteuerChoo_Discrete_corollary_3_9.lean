-- Prove2me | Theorems.Thm_SteuerChoo_Discrete_corollary_3_9
-- name    : SteuerChoo.Discrete.corollary_3_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:48:10.418317+00:00
-- url     : https://prove2.me/theorems/dfe3d52a-6d38-4620-9fc7-aaeaf9770417
-- title:
--   Corollary 3.9 — with ρ of (3.8), each zᵖ ∈ N uniquely minimizes the augmented program for λᵖ ∈ Λ̄
-- statement:
--   Let $k \ge 1$, let $Z \subset \mathbb R^k$ be finite with nondominated set $N$, let $z^*$ be an ideal criterion vector for $Z$, and let $\rho$ be the coefficient of (3.8), which depends on $Z$ and $z^*$ only. Then for every $z^p \in N$ the weights $\lambda^p$ of (b) lie in $\bar\Lambda = \{\lambda \in \mathbb R^k \mid \lambda_i \ge 0,\ \sum_i \lambda_i = 1\}$, and $z^p$ uniquely minimizes the augmented weighted Tchebycheff program with weights $\lambda^p$ and coefficient $\rho$: for every $z^q \in Z$, $z^q \ne z^p$,
--   $$\max_i \lambda^p_i(z^*_i - z^p_i) + \rho\, e^{\mathsf T}(z^* - z^p) \;<\; \max_i \lambda^p_i(z^*_i - z^q_i) + \rho\, e^{\mathsf T}(z^* - z^q).$$
--
--   A single augmentation coefficient $\rho$ thus serves every nondominated vector simultaneously; only the weights vary. This is what the interactive procedure uses.
--
--   **Formalization Note** The paper's "each $z^p \in N$ has a $\bar\lambda \in \bar\Lambda$" is stated with the witness $\bar\lambda = \lambda^p$, which is what "same as Theorem 3.4" means and is stronger than the bare existence. The paper's proof ("$0 < \rho \le \rho_p$") uses $\rho \le \rho_p$, which can fail under the empty-minimum convention (when the set in (3.6) is empty for $z^p$ but that of (3.8) is not); the statement itself remains true because any $\rho > 0$ works for such a $z^p$. $S$, $f$ and $\alpha$ are eliminated as in the definitions.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983) 326–344, https://doi.org/10.1007/BF02591870, p. 333, Corollary 3.9 (with eq. (3.8), p. 332)

import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

/-- **Corollary 3.9** (Steuer–Choo 1983, p. 333): with `ρ` of (3.8) in place of `ρ_p`, each
`zᵖ ∈ N` has a `λ̄ ∈ Λ̄` (namely `λᵖ` of (b)) such that `zᵖ` uniquely minimizes the augmented weighted
Tchebycheff program. `Z` is finite and `z*` is an ideal criterion vector. -/
theorem corollary_3_9 {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z) :
    lamP zstar zp ∈ stdSimplex ℝ (Fin k) ∧
      ∀ zq ∈ Z, zq ≠ zp →
        augTcheb (lamP zstar zp) (rho38 Z zstar) zstar zp <
          augTcheb (lamP zstar zp) (rho38 Z zstar) zstar zq := by sorry

end SteuerChoo.Discrete
