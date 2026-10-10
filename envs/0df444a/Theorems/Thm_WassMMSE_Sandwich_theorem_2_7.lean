-- Prove2me | Theorems.Thm_WassMMSE_Sandwich_theorem_2_7
-- name    : WassMMSE.Sandwich.theorem_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:45.296375+00:00
-- url     : https://prove2.me/theorems/ff23f8e4-8860-4d74-a59f-15138c22393c
-- title:
--   Theorem 2.7, p. 9 — the Gelbrich MMSE problem (2.1) equals the finite convex program (2.2), attained by an affine estimator
-- statement:
--   Let $\widehat{\mathbb P}_x\in\mathcal M(\mathbb R^n)$ and $\widehat{\mathbb P}_w\in\mathcal M(\mathbb R^m)$ be nominal distributions with means $\widehat\mu_x,\widehat\mu_w$ and covariance matrices $\widehat\Sigma_x,\widehat\Sigma_w$, let $H\in\mathbb R^{m\times n}$ and $\rho_x,\rho_w\ge0$.
--
--   1. The optimal value of the Gelbrich MMSE estimation problem (2.1), $\inf_{\psi\in\mathcal A}\sup_{\mathbb Q\in\mathbb G(\widehat{\mathbb P})}\mathcal R(\psi,\mathbb Q)$, equals the infimum of the finite convex program
--   $$\begin{aligned}\inf\ &\gamma_x(\rho_x^2-\operatorname{Tr}[\widehat\Sigma_x])+\gamma_x^2\big\langle[\gamma_xI_n-(I_n-AH)^\top(I_n-AH)]^{-1},\widehat\Sigma_x\big\rangle\\&+\gamma_w(\rho_w^2-\operatorname{Tr}[\widehat\Sigma_w])+\gamma_w^2\big\langle(\gamma_wI_m-A^\top A)^{-1},\widehat\Sigma_w\big\rangle\\ \text{s.t. }&A\in\mathbb R^{n\times m},\ \gamma_x,\gamma_w\ge0,\ \gamma_xI_n-(I_n-AH)^\top(I_n-AH)\succ0,\ \gamma_wI_m-A^\top A\succ0.\end{aligned}\tag{2.2}$$
--   2. If $\rho_x>0$ and $\rho_w>0$, there is $A^\star$ that solves (2.2), in the sense that adding the constraint $A=A^\star$ does not change the infimum of (2.2), and the affine estimator $\psi^\star(y)=A^\star y+b^\star$ with $b^\star=\widehat\mu_x-A^\star(H\widehat\mu_x+\widehat\mu_w)$ attains the infimum of (2.1).
--
--   The theorem turns the infinite-dimensional minimax problem over affine estimators and distributions into a finite convex program that can be solved in polynomial time; it is the primal half of the sandwich theorem.
--
--   **Formalization Note** The value of (2.1) lies in $[0,\infty]$ and is compared with the `EReal` infimum of (2.2) through the coercion $[0,\infty]\to\overline{\mathbb R}$. "Equivalent" on the page is read as equality of optimal values together with the attainment statement. The theorem is stated for general nominal distributions with finite second moments, as in Section 2; their moments enter through the published `meanVector` and `covarianceMatrix`.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 9, Theorem 2.7 and (2.2), footnote 1

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_meanVector
import Definitions.Def_WassersteinDRO_Gelbrich_covarianceMatrix
import Definitions.Def_WassMMSE_Sandwich_Setting
import Definitions.Def_WassMMSE_Sandwich_Programs

open MeasureTheory ProbabilityTheory WassersteinDRO.Gelbrich

namespace WassMMSE.Sandwich

/-- Theorem 2.7 (Gelbrich MMSE estimation problem; arXiv:1911.03539v2, p. 9). For nominal marginals
`ℙ̂_x ∈ 𝓜(ℝⁿ)`, `ℙ̂_w ∈ 𝓜(ℝᵐ)` with moments `(μ̂_x, Σ̂_x)`, `(μ̂_w, Σ̂_w)` and radii `ρ_x, ρ_w ≥ 0`:
1. the optimal value of (2.1) equals the infimum of the finite program (2.2);
2. if `ρ_x, ρ_w > 0`, some `A⋆` solves (2.2) (fixing `A = A⋆` leaves the infimum unchanged), and
   the affine estimator `ψ⋆(y) = A⋆y + b⋆`, `b⋆ = μ̂_x − A⋆(Hμ̂_x + μ̂_w)`, attains the infimum of
   (2.1). -/
theorem theorem_2_7 {n m : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) (ρx ρw : ℝ) (hρx : 0 ≤ ρx)
    (hρw : 0 ≤ ρw) (Px : Measure (E n)) (Pw : Measure (E m)) (hPx : HasFiniteSecondMoment Px)
    (hPw : HasFiniteSecondMoment Pw) :
    let μx := meanVector Px
    let Shx := covarianceMatrix Px
    let μw := meanVector Pw
    let Shw := covarianceMatrix Pw
    ((gelbrichMinimax H ρx ρw μx Shx μw Shw : ENNReal) : EReal) =
        gelbrichProgramValue H ρx ρw Shx Shw ∧
    (0 < ρx → 0 < ρw →
      ∃ Astar : Matrix (Fin n) (Fin m) ℝ,
        (⨅ (γx : ℝ) (γw : ℝ) (_ : IsGelbrichProgramFeasible H Astar γx γw),
            (gelbrichProgramObjective H ρx ρw Shx Shw Astar γx γw : EReal)) =
          gelbrichProgramValue H ρx ρw Shx Shw ∧
        let ψstar : E m → E n := fun y =>
          Matrix.toEuclideanLin Astar y +
            (μx - Matrix.toEuclideanLin Astar (Matrix.toEuclideanLin H μx + μw))
        IsAffineEstimator ψstar ∧
          (⨆ (Q : Measure (E n × E m)) (_ : Q ∈ gelbrichSet ρx ρw μx Shx μw Shw),
              risk H ψstar Q) = gelbrichMinimax H ρx ρw μx Shx μw Shw) := by sorry

end WassMMSE.Sandwich
