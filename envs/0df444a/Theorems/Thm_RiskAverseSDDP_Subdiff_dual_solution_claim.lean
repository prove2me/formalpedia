-- Prove2me | Theorems.Thm_RiskAverseSDDP_Subdiff_dual_solution_claim
-- name    : RiskAverseSDDP.Subdiff.dual_solution_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T04:32:13.598154+00:00
-- url     : https://prove2.me/theorems/2e2c7ba4-95e2-4515-829a-ddec9dc212da
-- title:
--   End of proof of Lemma 2.1, p. 5, with (2.7)-(b) — primal-dual solutions satisfy (2.7)-(b), and (2.7)-(b) with μ ≥ 0 gives (λ, μ) ∈ Λ(x₀)
-- statement:
--   Let $f:\mathbb R^m\times\mathbb R^n\to\mathbb R$ and $g_1,\dots,g_p:\mathbb R^m\times\mathbb R^n\to\mathbb R$ be real-valued, convex and differentiable, let $Y$ be nonempty, compact and convex, and let $y_0\in S(x_0)$ be a feasible point of the program (2.1). Write $I=I(x_0,y_0)$ and, for $\lambda\in\mathbb R^q$, $\mu\in\mathbb R^p$, consider condition (2.7)-(b):
--   $$-\Big[\nabla_y f(x_0,y_0)+B^\top\lambda+\sum_{i\in I}\mu_i\nabla_y g_i(x_0,y_0)\Big]\in\mathcal N_Y(y_0).$$
--   1. If $y_0\in\operatorname{Sol}(x_0)$, $(\lambda,\mu)\in\Lambda(x_0)$ and there is no duality gap, $\theta_{x_0}(\lambda,\mu)=\mathcal Q(x_0)$ (so $(y_0,\lambda,\mu)$ is a primal-dual solution), then (2.7)-(b) holds.
--   2. If $\mu\ge 0$, $\mu_i=0$ for $i\notin I$, and (2.7)-(b) holds, then $(\lambda,\mu)\in\Lambda(x_0)$.
--
--   This is the closing remark of the proof of Lemma 2.1; it converts the multipliers of (2.4) in the differentiable case into dual solutions of (2.3), and conversely.
--
--   **Formalization Note** In (2.7)-(b) the page takes $\mu\in\mathbb R^{|I(x_0,y_0)|}_+$; here $\mu\in\mathbb R^p$ and part 2 requires $\mu$ to vanish off $I$, i.e. it is extended by $0$ to $\mathbb R^p_+$. Part 2 assumes only that $y_0$ is primal feasible, as the page says ("knowing that $y_0$ is primal feasible"); part 1 assumes $y_0\in\operatorname{Sol}(x_0)$, as a primal-dual solution requires. A *primal-dual solution* is taken to mean $y_0\in\operatorname{Sol}(x_0)$, $(\lambda,\mu)\in\Lambda(x_0)$ and $\theta_{x_0}(\lambda,\mu)=\mathcal Q(x_0)$. Partial gradients are `gradient` of the sections $y\mapsto f(x_0,y)$, $y\mapsto g_i(x_0,y)$.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 5 (end of the proof of Lemma 2.1) and p. 4, (2.7)-(b)

import Mathlib
import Definitions.Def_RiskAverseSDDP_Subdiff_Model
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

open scoped RealInnerProductSpace

namespace RiskAverseSDDP.Subdiff

open ConvexProgram

/-- End of the proof of Lemma 2.1, p. 5, with (2.7)-(b), p. 4: let `f` and the `g_i` be
real-valued, convex and differentiable, `Y` nonempty, compact and convex, and `y₀ ∈ S(x₀)`
primal feasible.
(i) If `y₀ ∈ Sol(x₀)` (`f(x₀, y₀) = 𝒬(x₀)`) and `(λ, μ) ∈ Λ(x₀)` with no duality gap
(`θ_{x₀}(λ, μ) = 𝒬(x₀)`), then
`-[∇_y f(x₀, y₀) + Bᵀλ + Σ_{i ∈ I(x₀,y₀)} μ_i ∇_y g_i(x₀, y₀)] ∈ 𝒩_Y(y₀)` (2.7)-(b).
(ii) If `μ ≥ 0` vanishes outside `I(x₀, y₀)` and `(y₀, λ, μ)` satisfies (2.7)-(b), then
`(λ, μ) ∈ Λ(x₀)`. -/
theorem dual_solution_claim {m n q p : ℕ} (P : ConvexProgram m n q p)
    (fr : E m × E n → ℝ) (gr : Fin p → E m × E n → ℝ)
    (hfr : ∀ z, P.f z = (fr z : EReal)) (hgr : ∀ i z, P.g i z = (gr i z : EReal))
    (hfc : ConvexOn ℝ Set.univ fr) (hfd : Differentiable ℝ fr)
    (hgc : ∀ i, ConvexOn ℝ Set.univ (gr i)) (hgd : ∀ i, Differentiable ℝ (gr i))
    (hY : P.Y.Nonempty ∧ IsCompact P.Y ∧ Convex ℝ P.Y)
    (x₀ : E m) (y₀ : E n) (hy₀ : y₀ ∈ P.S x₀) :
    (P.f (x₀, y₀) = P.Q x₀ →
      ∀ (lam : E q) (μ : Fin p → ℝ), (lam, μ) ∈ P.Lambda x₀ → P.theta x₀ lam μ = P.Q x₀ →
      -(gradient (fun y => fr (x₀, y)) y₀ + Matrix.toEuclideanLin P.B.transpose lam +
          ∑ i ∈ P.active x₀ y₀, μ i • gradient (fun y => gr i (x₀, y)) y₀) ∈
        FirstOrderOpt.ConvexTheory.normalCone P.Y y₀) ∧
    (∀ (lam : E q) (μ : Fin p → ℝ), 0 ≤ μ → (∀ i, i ∉ P.active x₀ y₀ → μ i = 0) →
      -(gradient (fun y => fr (x₀, y)) y₀ + Matrix.toEuclideanLin P.B.transpose lam +
          ∑ i ∈ P.active x₀ y₀, μ i • gradient (fun y => gr i (x₀, y)) y₀) ∈
        FirstOrderOpt.ConvexTheory.normalCone P.Y y₀ →
      (lam, μ) ∈ P.Lambda x₀) := by sorry

end RiskAverseSDDP.Subdiff
