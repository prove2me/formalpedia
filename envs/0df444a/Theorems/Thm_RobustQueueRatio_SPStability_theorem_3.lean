-- Prove2me | Theorems.Thm_RobustQueueRatio_SPStability_theorem_3
-- name    : RobustQueueRatio.SPStability.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:24:01.910964+00:00
-- url     : https://prove2.me/theorems/8490a8de-2cd8-498a-a0ad-3b423a54801d
-- title:
--   Theorem 3: completely-$\mathcal S$ at every static-priority corner, with one determinant sign, implies completely-$\mathcal S$ for every ratio matrix
-- statement:
--   Fix an open multiclass network $(C,M,P,\alpha)$ with $Q=(I-P^\top)^{-1}$. Suppose that:
--
--   1. for every static-priority ratio matrix $\Delta$, $R^{-1}_\Delta=CMQ\Delta$ is invertible and $R_\Delta=(CMQ\Delta)^{-1}$ is completely-$\mathcal S$; and
--   2. all the determinants $\det(R^{-1}_\Delta)$, over static-priority $\Delta$, have the same sign.
--
--   Then for every ratio matrix $\Delta$,
--
--   $$
--   CMQ\Delta\ \text{is invertible and}\ R_\Delta\ \text{is completely-}\mathcal S .
--   $$
--
--   Since completely-$\mathcal S$ is equivalent to existence of solutions of the Skorohod problem, the theorem says that if the Skorohod problem is well posed at the static-priority corners, it is well posed for every queue-ratio policy.
--
--   **Formalization Note.** "All have the same sign" is the disjunction: either $\det(CMQ\Delta)>0$ for every static-priority $\Delta$, or $\det(CMQ\Delta)<0$ for every static-priority $\Delta$. The conclusion states invertibility explicitly, since Lean's inverse of a singular matrix is $0$.
-- source:
--   Zhao, Gurvich & Hasenbein, A Hierarchical Approach to Robust Stability of Multiclass Queueing Networks, arXiv:2303.17746v3, p. 11, Theorem 3

import Mathlib
import Definitions.Def_RobustQueueRatio_SPStability_Network
import Definitions.Def_RobustQueueRatio_SPStability_ChenS
import Definitions.Def_RobustQueueRatio_SPStability_RatioMatrix

open Matrix

namespace RobustQueueRatio.SPStability

/-- Theorem 3 (Zhao, Gurvich & Hasenbein, arXiv:2303.17746v3, p. 11). If for every
static-priority `Δ` (i) `R_Δ⁻¹ = CMQΔ` is invertible and `R_Δ` is completely-S, and (ii) all
`det(R_Δ⁻¹)` have the same sign, then for every ratio matrix `Δ`, `R_Δ⁻¹` is invertible and `R_Δ`
is completely-S. -/
theorem theorem_3 {J K : ℕ} (N : Network J K)
    (hcorner : ∀ Δ, IsStaticPriority N Δ →
      IsUnit (reflInv N Δ).det ∧ IsCompletelyS (refl N Δ))
    (hsign : (∀ Δ, IsStaticPriority N Δ → 0 < (reflInv N Δ).det) ∨
      (∀ Δ, IsStaticPriority N Δ → (reflInv N Δ).det < 0)) :
    ∀ Δ, IsRatioMatrix N Δ → IsUnit (reflInv N Δ).det ∧ IsCompletelyS (refl N Δ) := by sorry

end RobustQueueRatio.SPStability
