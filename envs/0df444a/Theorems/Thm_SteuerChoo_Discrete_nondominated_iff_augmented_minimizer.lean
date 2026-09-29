-- Prove2me | Theorems.Thm_SteuerChoo_Discrete_nondominated_iff_augmented_minimizer
-- name    : SteuerChoo.Discrete.nondominated_iff_augmented_minimizer
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:48:41.964993+00:00
-- url     : https://prove2.me/theorems/d09c6827-4dd8-4f44-9bba-f68163543d9b
-- title:
--   Theorem 3.7 — zᵖ ∈ N iff zᵖ minimizes the augmented weighted Tchebycheff program (ρ of (3.8)) for some λ ∈ Λ̄
-- statement:
--   Let $k \ge 1$, let $Z \subset \mathbb R^k$ be a finite set of criterion vectors with nondominated set $N$, let $z^*$ be an ideal criterion vector for $Z$, and let
--   $$\rho = \tfrac12 \min_{z^i \in N} \Big[ \min_{z^j \in Z} \Big\{ \frac{\alpha_{ij} - \alpha_{ii}}{e^{\mathsf T}(z^j - z^i)} \;\Big|\; e^{\mathsf T}(z^j - z^i) > 0 \Big\} \Big] \tag{3.8}$$
--   with $\alpha_{ij} = \max_l \lambda^i_l (z^*_l - z^j_l)$ for the weights $\lambda^i$ of (b). Then for every $z^p \in Z$:
--   $$z^p \in N \iff \exists\, \lambda \in \bar\Lambda \ \ \forall z \in Z:\ \ \max_i \lambda_i(z^*_i - z^p_i) + \rho\, e^{\mathsf T}(z^* - z^p) \le \max_i \lambda_i(z^*_i - z_i) + \rho\, e^{\mathsf T}(z^* - z),$$
--   where $\bar\Lambda = \{\lambda \in \mathbb R^k \mid \lambda_i \ge 0,\ \sum_{i=1}^k \lambda_i = 1\}$. In words: a criterion vector is nondominated exactly when it minimizes the augmented weighted Tchebycheff program $\min\{\alpha + \rho e^{\mathsf T}(z^*-z)\}$ s.t. $\alpha \ge \lambda_i(z^*_i - z_i)$, $z \in Z$, for some weight vector $\lambda$.
--
--   This is the characterization behind the interactive weighted Tchebycheff procedure in the discrete case: with one fixed $\rho$, varying $\lambda$ over $\bar\Lambda$ reaches every nondominated vector, including unsupported ones that no weighted-sum program can reach, and never returns a dominated one.
--
--   **Formalization Note** The paper says "Let $N$ be finite", but (3.8) ranges over $Z$ and the proof invokes Theorem 3.4, which assumes $Z$ finite; the formalization takes $Z$ finite (the section's standing discrete assumption). $S$, $f$ and the program variable $\alpha$ are eliminated: the objective at $z$ with minimal $\alpha$ is $\max_i \lambda_i(z^*_i - z_i) + \rho e^{\mathsf T}(z^*-z)$. $z^*$ is an ideal criterion vector (the paper's standing assumption) and $k \ge 1$. When (3.8) ranges over an empty set, $\rho$ is set to $1$.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983) 326–344, https://doi.org/10.1007/BF02591870, p. 332, Theorem 3.7, eq. (3.8)

import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

/-- **Theorem 3.7** (Steuer–Choo 1983, p. 332): let `Z` be finite, `z*` an ideal criterion vector
and `ρ` as in (3.8). Then for `zᵖ ∈ Z`: `zᵖ ∈ N` if and only if there exists `λ ∈ Λ̄` such that `zᵖ`
minimizes the augmented weighted Tchebycheff program over `Z`. -/
theorem nondominated_iff_augmented_minimizer {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ))
    (zstar : Fin k → ℝ) (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hzp : zp ∈ Z) :
    zp ∈ nondominated Z ↔
      ∃ lam ∈ stdSimplex ℝ (Fin k),
        ∀ z ∈ Z, augTcheb lam (rho38 Z zstar) zstar zp ≤ augTcheb lam (rho38 Z zstar) zstar z := by sorry

end SteuerChoo.Discrete
