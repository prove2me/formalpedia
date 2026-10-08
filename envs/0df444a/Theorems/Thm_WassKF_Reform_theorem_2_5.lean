-- Prove2me | Theorems.Thm_WassKF_Reform_theorem_2_5
-- name    : WassKF.Reform.theorem_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:11:58.753079+00:00
-- url     : https://prove2.me/theorems/b6aac497-30f8-4b22-b2dc-4c0918e0d12b
-- title:
--   Theorem 2.5 — the minimax MMSE problem (2) over the Gaussian Wasserstein ball equals program (5); ψ⋆ is affine and N(µ, S⋆) is least favorable
-- statement:
--   Let $z = [x; y]$ with $x \in \mathbb R^n$, $y \in \mathbb R^m$ and $d = n + m$. Let $\mathbb P = \mathcal N_d(\mu, \Sigma)$ with $\mu = [\mu_x; \mu_y]$ and $\Sigma \succ 0$, let $\underline\sigma = \lambda_{\min}(\Sigma) > 0$, let $\rho \ge 0$, and let $\mathcal P = \{\mathbb Q \in \mathcal N_d : W_2(\mathbb Q, \mathbb P) \le \rho\}$ be the Wasserstein ambiguity set (3). Let $\mathcal L$ be the family of all measurable functions $\mathbb R^m \to \mathbb R^n$. Consider the finite program
--
--   $$
--   \begin{aligned}
--   \sup \quad & \operatorname{Tr}\bigl[S_{xx} - S_{xy} S_{yy}^{-1} S_{yx}\bigr] \\
--   \text{s.t.} \quad & S = \begin{bmatrix} S_{xx} & S_{xy} \\ S_{yx} & S_{yy}\end{bmatrix} \in \mathbb S^d_+,\quad S_{xx} \in \mathbb S^n_+,\quad S_{yy} \in \mathbb S^m_+, \\
--   & \operatorname{Tr}\Bigl[S + \Sigma - 2\bigl(\Sigma^{1/2} S \Sigma^{1/2}\bigr)^{1/2}\Bigr] \le \rho^2, \quad S \succeq \underline\sigma I_d .
--   \end{aligned}
--   \tag{5}
--   $$
--
--   Then the minimax problem (2) is equivalent to (5) in the following sense.
--
--   1. The optimal value of (2), $\inf_{\psi \in \mathcal L} \sup_{\mathbb Q \in \mathcal P} \mathbb E^{\mathbb Q}[\|x - \psi(y)\|^2]$, equals the optimal value of (5).
--   2. If $S^\star$ is optimal in (5), then the affine function
--   $$
--   \psi^\star(y) = S^\star_{xy} (S^\star_{yy})^{-1} (y - \mu_y) + \mu_x
--   $$
--   is measurable and attains the infimum in (2): it is a distributionally robust minimum mean square error estimator.
--   3. For the same $S^\star$, the normal distribution $\mathbb Q^\star = \mathcal N_d(\mu, S^\star)$ belongs to $\mathcal P$ and attains the supremum in nature's problem $\sup_{\mathbb Q \in \mathcal P} \inf_{\psi \in \mathcal L} \mathbb E^{\mathbb Q}[\|x - \psi(y)\|^2]$: it is the least favorable prior.
--
--   The theorem reduces an infinite-dimensional minimax problem over a nonconvex set of distributions to a finite program over covariance matrices, and recovers both the robust estimator and the least favorable prior from its optimal solution.
--
--   **Formalization Note** "Equivalent" is not defined on the page; it is read as items 1–3, which cover both sentences of the theorem. Values of (2) and of nature's problem are in $[0,\infty]$ (lower Lebesgue integrals); the value of (5) is the published `sdpValue` in `EReal`, compared through the coercion $[0,\infty] \to$ `EReal`. Program (5) is the published `sdpFeasibleSet ρ Σ σ` with objective `sdpObjective`; $S_{xy} = S_{yx}^\top$ holds by symmetry of $S$. $\underline\sigma$ is passed as the least eigenvalue of $\Sigma$. The word "convex" in "finite convex program" is not part of the formal statement. Neither existence nor uniqueness of an optimal $S^\star$ is asserted: items 2 and 3 hold for every optimal $S^\star$. On the feasible set $S \succeq \underline\sigma I_d$ with $\underline\sigma > 0$, so $S_{yy}$ is invertible and the matrix inverse has no junk value. $\psi^\star$ is the published `affineEstimator`.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 3, Theorem 2.5, (5)

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_sdpFeasibleSet
import Definitions.Def_WassersteinDRO_Shrinkage_sdpObjective
import Definitions.Def_WassersteinDRO_Shrinkage_sdpValue
import Definitions.Def_WassersteinDRO_Shrinkage_affineEstimator
import Definitions.Def_WassKF_Reform_GaussianBall
import Definitions.Def_WassKF_Reform_expectedLoss
import Definitions.Def_WassKF_Reform_minimaxValue
import Definitions.Def_WassKF_Reform_maximinValue

open MeasureTheory ProbabilityTheory

namespace WassKF.Reform

/-- Theorem 2.5 (Tractable reformulation), Shafieezadeh-Abadeh et al., arXiv:1809.08830v3, p. 3.
Let `ℙ = 𝒩_d(μ, Sig)` with `Sig ≻ 0`, `ρ ≥ 0`, and `σ = λ_min(Sig)`. Then
1. the optimal value of the minimax problem (2) over the ambiguity set (3) equals the optimal value
   of program (5), `sup Tr[S_xx − S_xy S_yy⁻¹ S_yx]` over `sdpFeasibleSet ρ Sig σ`;
2. for every optimal solution `S⋆` of (5), the affine estimator
   `ψ⋆(y) = S⋆_xy (S⋆_yy)⁻¹ (y − μ_y) + μ_x` is measurable and attains the outer infimum of (2);
3. for the same `S⋆`, `Q⋆ = 𝒩_d(μ, S⋆)` lies in the ambiguity set and attains the outer supremum
   of nature's problem `sup_{Q ∈ 𝒫} inf_{ψ ∈ ℒ} E^Q[‖x − ψ(y)‖²]` (it is the least favorable prior).
Here `μ_x = (μ_i)_{i ∈ inl}` and `μ_y = (μ_j)_{j ∈ inr}`. -/
theorem theorem_2_5 {n m : ℕ} (μ : EuclideanSpace ℝ (Fin n ⊕ Fin m))
    (Sig : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) (hSig : Sig.PosDef)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (σ : ℝ) (hσ : IsLeast (Set.range hSig.isHermitian.eigenvalues) σ) :
    ((minimaxValue μ Sig ρ : ENNReal) : EReal) = WassersteinDRO.Shrinkage.sdpValue ρ Sig σ ∧
    ∀ Sstar ∈ WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sig σ,
      IsMaxOn WassersteinDRO.Shrinkage.sdpObjective
          (WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sig σ) Sstar →
        (Measurable (WassersteinDRO.Shrinkage.affineEstimator Sstar.toBlocks₁₂ Sstar.toBlocks₂₂
            ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => μ (Sum.inl i)))
            ((EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => μ (Sum.inr j)))) ∧
          (⨆ (Q : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin m))) (_ : Q ∈ GaussianBall μ Sig ρ),
              expectedLoss (WassersteinDRO.Shrinkage.affineEstimator Sstar.toBlocks₁₂
                Sstar.toBlocks₂₂
                ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => μ (Sum.inl i)))
                ((EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => μ (Sum.inr j)))) Q) =
            minimaxValue μ Sig ρ) ∧
        (multivariateGaussian μ Sstar ∈ GaussianBall μ Sig ρ ∧
          (⨅ (ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)) (_ : Measurable ψ),
              expectedLoss ψ (multivariateGaussian μ Sstar)) =
            maximinValue μ Sig ρ) := by sorry

end WassKF.Reform
