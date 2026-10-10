-- Prove2me | Theorems.Thm_RiskAverseSDDP_Subdiff_lemma_2_1_differentiable
-- name    : RiskAverseSDDP.Subdiff.lemma_2_1_differentiable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T04:32:20.689983+00:00
-- url     : https://prove2.me/theorems/3ec495ef-d3c2-4a15-a2bb-7e12fca96f60
-- title:
--   Lemma 2.1, differentiable case, p. 4 (repaired: strict Slater point) — ∂𝒬(x₀) = {∇ₓf + Aᵀλ + Σ_{i∈I} μ_i ∇ₓg_i : (λ, μ) ∈ Λ(x₀)}
-- statement:
--   Consider the program (2.1) with $X\subseteq\mathbb R^m$ and $Y\subseteq\mathbb R^n$ nonempty, compact and convex, and suppose $f$ and $g_1,\dots,g_p$ are real-valued, convex and differentiable on $\mathbb R^m\times\mathbb R^n$. Assume the repaired Slater condition: there is $(\bar x,\bar y)\in X\times\operatorname{ri}(Y)$ with $A\bar x+B\bar y=b$ and $g_i(\bar x,\bar y)<0$ for all $i$. Let $x_0\in X$ with $S(x_0)\ne\emptyset$. Then $\operatorname{Sol}(x_0)\ne\emptyset$, and for every $y_0\in\operatorname{Sol}(x_0)$
--   $$\partial\mathcal Q(x_0)=\Big\{\nabla_x f(x_0,y_0)+A^\top\lambda+\sum_{i\in I(x_0,y_0)}\mu_i\nabla_x g_i(x_0,y_0):\ (\lambda,\mu)\in\Lambda(x_0)\Big\}.$$
--
--   This is the "in particular" clause of Lemma 2.1: when the data are smooth, subgradients of the value function — the slopes of the cuts in SDDP — are obtained from any primal solution and any optimal dual multipliers.
--
--   **Formalization Note (repair).** "$f$ and $g$ are differentiable" is read literally: $f$ and the $g_i$ are real-valued and differentiable on the whole space, which makes (H) and the condition $(\bar x,\bar y)\in\operatorname{ri}(\operatorname{dom} f)$ automatic. The printed Slater-type condition $(\bar x,\bar y)\in\operatorname{ri}(C_2)$ is replaced by the strict inequalities $g_i(\bar x,\bar y)<0$; with $g(x,y)=y^2$, $f(x,y)=y$, $X=Y=[-1,1]$, $A=B=0$, $b=0$ the printed hypotheses hold while $\partial\mathcal Q(0)=\{0\}$ and the right-hand side is empty. In Lean the repaired condition is `RepairedSlater`, whose clause $(\bar x,\bar y)\in\operatorname{ri}(\operatorname{dom}f)$ is automatic here. $\nabla_x f(x_0,y_0)$ is `gradient (fun x => f (x, y₀)) x₀`.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 4, Lemma 2.1 (differentiable case; repaired hypotheses)

import Mathlib
import Definitions.Def_RiskAverseSDDP_Subdiff_Model
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

open scoped RealInnerProductSpace

namespace RiskAverseSDDP.Subdiff

open ConvexProgram

/-- Lemma 2.1, differentiable case, p. 4, repaired (strict Slater point for `g`): if `f` and
the `g_i` are real-valued, convex and differentiable on `ℝ^m × ℝ^n`, `X`, `Y` are nonempty,
compact and convex, `x₀ ∈ X`, `S(x₀) ≠ ∅`, and the repaired Slater condition holds, then
`Sol(x₀) ≠ ∅` and for every `y₀ ∈ Sol(x₀)`
`∂𝒬(x₀) = {∇_x f(x₀, y₀) + Aᵀλ + Σ_{i ∈ I(x₀,y₀)} μ_i ∇_x g_i(x₀, y₀) : (λ, μ) ∈ Λ(x₀)}`. -/
theorem lemma_2_1_differentiable {m n q p : ℕ} (P : ConvexProgram m n q p) (X : Set (E m))
    (hX : X.Nonempty ∧ IsCompact X ∧ Convex ℝ X)
    (hY : P.Y.Nonempty ∧ IsCompact P.Y ∧ Convex ℝ P.Y)
    (fr : E m × E n → ℝ) (gr : Fin p → E m × E n → ℝ)
    (hfr : ∀ z, P.f z = (fr z : EReal)) (hgr : ∀ i z, P.g i z = (gr i z : EReal))
    (hfc : ConvexOn ℝ Set.univ fr) (hfd : Differentiable ℝ fr)
    (hgc : ∀ i, ConvexOn ℝ Set.univ (gr i)) (hgd : ∀ i, Differentiable ℝ (gr i))
    (hSlater : P.RepairedSlater X)
    (x₀ : E m) (hx₀ : x₀ ∈ X) (hS : (P.S x₀).Nonempty) :
    (P.Sol x₀).Nonempty ∧ ∀ y₀ ∈ P.Sol x₀,
      subdiff P.Q x₀ =
        {s | ∃ (lam : E q) (μ : Fin p → ℝ), (lam, μ) ∈ P.Lambda x₀ ∧
          s = gradient (fun x => fr (x, y₀)) x₀ + Matrix.toEuclideanLin P.A.transpose lam +
            ∑ i ∈ P.active x₀ y₀, μ i • gradient (fun x => gr i (x, y₀)) x₀} := by sorry

end RiskAverseSDDP.Subdiff
