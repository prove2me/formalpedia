-- Prove2me | Theorems.Thm_RobustQueueRatio_SPStability_theorem_4
-- name    : RobustQueueRatio.SPStability.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:24:07.78541+00:00
-- url     : https://prove2.me/theorems/3d2bc5b8-d5a8-4b12-8754-cf5ac8b496da
-- title:
--   Theorem 4: Chen-$\mathcal S$ at every static-priority corner, with one determinant sign, implies Chen-$\mathcal S$ for every ratio matrix
-- statement:
--   Fix an open multiclass network $(C,M,P,\alpha)$ with $Q=(I-P^\top)^{-1}$ and traffic intensities $\rho=CMQ\alpha$. For a ratio matrix $\Delta$ write $R_\Delta=(CMQ\Delta)^{-1}$ and $\theta_\Delta=R_\Delta(\rho-e)$. Suppose that:
--
--   1. for every static-priority ratio matrix $\Delta$, $R^{-1}_\Delta=CMQ\Delta$ is invertible and $(R_\Delta,\theta_\Delta)$ is Chen-$\mathcal S$; and
--   2. all the determinants $\det(R^{-1}_\Delta)$, over static-priority $\Delta$, have the same sign.
--
--   Then for every ratio matrix $\Delta$,
--
--   $$
--   CMQ\Delta\ \text{is invertible and}\ (R_\Delta,\theta_\Delta)\ \text{is Chen-}\mathcal S .
--   $$
--
--   Chen-$\mathcal S$ of $(R_\Delta,\theta_\Delta)$ guarantees, by Chen (1996), stability of the Skorohod problem that the fluid model of the network follows under the queue-ratio policy $\Delta$ after state-space collapse. The theorem therefore reduces robust Skorohod-problem stability over the infinite family of queue-ratio policies to a check at the finitely many static-priority corners.
--
--   **Formalization Note.** "All have the same sign" is the disjunction: either $\det(CMQ\Delta)>0$ for every static-priority $\Delta$, or $\det(CMQ\Delta)<0$ for every static-priority $\Delta$. The conclusion states invertibility explicitly, since Lean's inverse of a singular matrix is $0$. The nominal-load condition $\rho<e$ is not assumed, as on the page. "Every ratio matrix" includes the nonnegativity $\delta\ge 0$ of the weights.
-- source:
--   Zhao, Gurvich & Hasenbein, A Hierarchical Approach to Robust Stability of Multiclass Queueing Networks, arXiv:2303.17746v3, p. 12, Theorem 4

import Mathlib
import Definitions.Def_RobustQueueRatio_SPStability_Network
import Definitions.Def_RobustQueueRatio_SPStability_ChenS
import Definitions.Def_RobustQueueRatio_SPStability_RatioMatrix

open Matrix

namespace RobustQueueRatio.SPStability

/-- Theorem 4 (Zhao, Gurvich & Hasenbein, arXiv:2303.17746v3, p. 12). If for every
static-priority ratio matrix `Δ` (i) `R_Δ⁻¹ = CMQΔ` is invertible and `(R_Δ, θ_Δ)` is Chen-S,
and (ii) all `det(R_Δ⁻¹)` have the same sign, then for every ratio matrix `Δ`, `R_Δ⁻¹` is
invertible and `(R_Δ, θ_Δ)` is Chen-S, where `θ_Δ = R_Δ(ρ − e)`. -/
theorem theorem_4 {J K : ℕ} (N : Network J K)
    (hcorner : ∀ Δ, IsStaticPriority N Δ →
      IsUnit (reflInv N Δ).det ∧ IsChenS (refl N Δ) (theta N Δ))
    (hsign : (∀ Δ, IsStaticPriority N Δ → 0 < (reflInv N Δ).det) ∨
      (∀ Δ, IsStaticPriority N Δ → (reflInv N Δ).det < 0)) :
    ∀ Δ, IsRatioMatrix N Δ → IsUnit (reflInv N Δ).det ∧ IsChenS (refl N Δ) (theta N Δ) := by sorry

end RobustQueueRatio.SPStability
