-- Prove2me | Theorems.Thm_PenaltyLag_Rate_theorem_5_1_iv
-- name    : PenaltyLag.Rate.theorem_5_1_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:11.432047+00:00
-- url     : https://prove2.me/theorems/546165d7-9b25-4885-a518-75fbf4f04b60
-- title:
--   Theorem 5.1 (iv) — L_r(·, y) has a unique minimizer ξ(y) over X, C¹ in y, with ∂ξ/∂yᵢ given by (5.5)
-- statement:
--   Assume the standing assumptions of §5 for $(\bar x, \bar y)$, with $X \subset \mathbb R^n$ convex, $f_0, \dots, f_m$ convex on $X$, and $I = \{i : f_i(\bar x) = 0\}$. For every $r > 0$ there are $\varepsilon > 0$ and a map $\xi : \mathbb R^m \to \mathbb R^n$ such that for every $y$ with $\sup g_r - g_r(y) \le \varepsilon$ (5.2):
--
--   1. $L_r(\cdot, y)$ attains its minimum over $X$ at the unique point $\xi(y) \in X$;
--   2. $\xi$ is continuously differentiable at $y$;
--   3. $\nabla_x^2 L_r(\xi(y), y)$ is positive definite (hence invertible);
--   4. the partial derivatives of $\xi$ are
--   $$
--   \frac{\partial \xi(y)}{\partial y_i} = \begin{cases} -\nabla_x^2 L_r(\xi(y), y)^{-1} \nabla f_i(\xi(y)) & \text{if } i \in I, \\ 0 & \text{if } i \notin I. \end{cases} \qquad (5.5)
--   $$
--
--   The map $y \mapsto \xi(y)$ is the primal point the dual method recovers from a dual iterate, and (5.5) is what turns dual convergence rates into primal ones.
--
--   **Formalization Note** In the paper (iv) is one of the conclusions of Theorem 5.1, valid for all $y, x$ satisfying (5.2)–(5.3) with $\varepsilon, \alpha$ chosen after arbitrary $r, \beta > 0$; since (iv) involves only $y$ and an $x$ satisfying (5.3) exists whenever $g_r(y)$ is finite, it is stated here for every $y$ satisfying (5.2). Positive definiteness of $\nabla_x^2 L_r(\xi(y), y)$ (the paper's (iii) at $x = \xi(y)$) is included so that `ContinuousLinearMap.inverse`, which returns $0$ for a non-invertible map, is the genuine inverse. $\partial \xi/\partial y_i$ is the derivative of $\xi$ at $y$ applied to the $i$-th unit vector; "the convex function $L_r(\cdot, y)$" (convexity is Theorem 3.1) is not restated. Indices are 0-based.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), p. 369, Theorem 5.1 (iv), (5.5)

import Mathlib
import Definitions.Def_PenaltyLag_Rate_Basic

open Filter Topology

namespace PenaltyLag.Rate

/-- Theorem 5.1 (iv), p. 369: for every r > 0 there are ε > 0 and a map ξ such that for every y with
sup g_r − g_r(y) ≤ ε (5.2), L_r(·, y) attains its minimum over X at the unique point ξ(y), ξ is C¹
at y, ∇²_x L_r(ξ(y), y) is positive definite, and (5.5) holds:
∂ξ(y)/∂yᵢ = −∇²_x L_r(ξ(y), y)⁻¹ ∇fᵢ(ξ(y)) for i ∈ I and 0 for i ∉ I. -/
theorem theorem_5_1_iv
    {n m : ℕ} (X : Set (Pt n)) (hX : Convex ℝ X)
    (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (xbar : Pt n) (ybar : Mult m) (hA : Sec5Assumptions X f₀ f xbar ybar)
    (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ξ : Mult m → Pt n, ∀ y : Mult m,
      (⨆ y' : Mult m, gr X f₀ f r y') - gr X f₀ f r y ≤ (ε : EReal) →
      (ξ y ∈ X ∧ ∀ x ∈ X, x ≠ ξ y → Lr f₀ f r (ξ y) y < Lr f₀ f r x y) ∧
      ContDiffAt ℝ 1 ξ y ∧
      (∀ z : Pt n, z ≠ 0 → 0 < hessForm (fun x' => Lr f₀ f r x' y) (ξ y) z) ∧
      ∀ i : Fin m, fderiv ℝ ξ y (EuclideanSpace.single i 1) =
        if i ∈ activeSet f xbar then
          -(ContinuousLinearMap.inverse (fderiv ℝ (gradient (fun x' => Lr f₀ f r x' y)) (ξ y))
              (gradient (f i) (ξ y)))
        else 0 := by sorry

end PenaltyLag.Rate
