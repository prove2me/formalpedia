-- Prove2me | Theorems.Thm_WassInvCov_Shrinkage_pd_case_optimal_in_6
-- name    : WassInvCov.Shrinkage.pd_case_optimal_in_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:34.657989+00:00
-- url     : https://prove2.me/theorems/c98ecb0d-061b-4a8a-bfe5-e137865ce5e1
-- title:
--   Proof of Theorem 3.1, p. 12, case Σ̂ ≻ 0 — (X⋆, γ⋆) is feasible and optimal in the convex program (6)
-- statement:
--   Let $p\ge1$, $\rho>0$, and let $\widehat\Sigma\in\mathbb S^p_{++}$ have the spectral decomposition $\widehat\Sigma=\sum_{i=1}^p\lambda_iv_iv_i^\top$ with orthonormal $v_1,\dots,v_p$. Let $\gamma^\star>0$ solve (16b) and $X^\star=\sum_{i=1}^px^\star_iv_iv_i^\top$ with $x^\star_i$ from (16a). Then $\gamma^\star I\succ X^\star\succ0$, and for every $X\succ0$ and $\gamma$ with $\gamma I\succ X$,
--
--   $$-\log\det X^\star+\gamma^\star(\rho^2-\operatorname{Tr}[\widehat\Sigma])+(\gamma^\star)^2\langle(\gamma^\star I-X^\star)^{-1},\widehat\Sigma\rangle\ \le\ -\log\det X+\gamma(\rho^2-\operatorname{Tr}[\widehat\Sigma])+\gamma^2\langle(\gamma I-X)^{-1},\widehat\Sigma\rangle.$$
--
--   That is, $(X^\star,\gamma^\star)$ is feasible and optimal in (6) with $\mathcal X=\mathbb S^p_{++}$. Together with Theorem 2.6 this proves Theorem 3.1 for positive definite $\widehat\Sigma$.
--
--   **Formalization Note** $p\ge1$ is added, as in the goal. The hypothesis $\widehat\Sigma\succ0$ is the page's: for singular $\widehat\Sigma$ the pair $(X^\star,\gamma^\star)$ is infeasible in (6).
-- source:
--   Nguyen, Kuhn & Mohajerin Esfahani, Distributionally Robust Inverse Covariance Estimation, arXiv:1805.07194v1, pp. 12–13, proof of Theorem 3.1, case Σ̂ ≻ 0

import Mathlib
import Definitions.Def_WassInvCov_Shrinkage_Setting

open MeasureTheory ProbabilityTheory Matrix

namespace WassInvCov.Shrinkage

/-- Proof of Theorem 3.1, p. 12, the case `Σ̂ ≻ 0` (arXiv:1805.07194v1): for `ρ > 0`, `Σ̂ ≻ 0` with an
orthonormal eigendecomposition `Σ̂ = Σᵢ λᵢ vᵢ vᵢᵀ`, and the positive root `γ⋆` of (16b), the pair
`(X⋆, γ⋆)` with `X⋆ = Σᵢ x⋆ᵢ vᵢ vᵢᵀ` is feasible (`γ⋆I ≻ X⋆ ≻ 0`) and optimal in (6) with
`𝒳 = 𝕊^p_{++}`. -/
theorem pd_case_optimal_in_6 {p : ℕ} (hp : 0 < p) (ρ : ℝ) (hρ : 0 < ρ)
    (Sh : Matrix (Fin p) (Fin p) ℝ) (hSh : Sh.PosDef) (lam : Fin p → ℝ)
    (v : Fin p → EuclideanSpace ℝ (Fin p)) (hv : Orthonormal ℝ v)
    (hdecomp : Sh = ∑ i, lam i • Matrix.vecMulVec (v i).ofLp (v i).ofLp)
    (γs : ℝ) (hγs : 0 < γs) (hroot : phi16b ρ lam γs = 0) :
    (γs • (1 : Matrix (Fin p) (Fin p) ℝ) - shrinkageEstimator lam v γs).PosDef ∧
    (shrinkageEstimator lam v γs).PosDef ∧
    ∀ (X : Matrix (Fin p) (Fin p) ℝ) (γ : ℝ), X.PosDef →
      (γ • (1 : Matrix (Fin p) (Fin p) ℝ) - X).PosDef →
      obj6 ρ Sh (shrinkageEstimator lam v γs) γs ≤ obj6 ρ Sh X γ := by sorry

end WassInvCov.Shrinkage
