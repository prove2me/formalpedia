-- Prove2me | Theorems.Thm_PenaltyLag_Rate_theorem_5_1_v
-- name    : PenaltyLag.Rate.theorem_5_1_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:47.70044+00:00
-- url     : https://prove2.me/theorems/59b65ab3-44c7-4719-8895-b95b285f9a06
-- title:
--   Theorem 5.1 (v) — g_r is C² near ȳ with negative definite Hessian given by (5.6)–(5.7)
-- statement:
--   Assume the standing assumptions of §5 for $(\bar x, \bar y)$, with $X \subset \mathbb R^n$ convex, $f_0, \dots, f_m$ convex on $X$, and $I = \{i : f_i(\bar x) = 0\}$. For every $r > 0$ there are $\varepsilon > 0$ and a map $\xi : \mathbb R^m \to \mathbb R^n$ such that for every $y$ with $\sup g_r - g_r(y) \le \varepsilon$ (5.2): $\xi(y)$ is the unique minimizer of $L_r(\cdot, y)$ over $X$, $\nabla_x^2 L_r(\xi(y), y)$ is positive definite, $g_r(y)$ is finite, $g_r$ is twice continuously differentiable at $y$, the Hessian $\nabla^2 g_r(y)$ is negative definite, and for every $w \in \mathbb R^m$
--   $$
--   w \cdot \nabla^2 g_r(y) w = -[A(y)w] \cdot \nabla_x^2 L_r(\xi(y), y)^{-1} [A(y) w] - \frac{1}{2r} \sum_{i \notin I} w_i^2, \qquad (5.6)
--   $$
--   where
--   $$
--   A(y) w = \sum_{i \in I} w_i \nabla f_i(\xi(y)). \qquad (5.7)
--   $$
--
--   Negative definiteness of $\nabla^2 g_r$ near $\bar y$ is what makes the dual problem well conditioned for unconstrained maximization and gives the quadratic estimates (5.17).
--
--   **Formalization Note** As for (iv), the conclusion is stated for every $y$ satisfying (5.2), with $\varepsilon$ chosen after $r$. "With $\xi(y)$ as in (iv)" is made self-contained by repeating the defining property of $\xi$ and the positive definiteness of $\nabla_x^2 L_r(\xi(y), y)$, which makes `ContinuousLinearMap.inverse` genuine. $g_r$ is in `EReal`; its finiteness is asserted, and the derivatives are those of its real-valued version `grR`. The Hessian form of $g_r$ is the derivative of its gradient. Indices are 0-based.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), p. 369, Theorem 5.1 (v), (5.6)–(5.7)

import Mathlib
import Definitions.Def_PenaltyLag_Rate_Basic

open Filter Topology

namespace PenaltyLag.Rate

/-- Theorem 5.1 (v), p. 369: for every r > 0 there are ε > 0 and a map ξ (the unique minimizer of
L_r(·, y) over X, as in (iv)) such that for every y with sup g_r − g_r(y) ≤ ε (5.2), g_r(y) is
finite, g_r is C² at y, ∇²g_r(y) is negative definite, and (5.6) holds with A(y)w = Σ_{i∈I} wᵢ ∇fᵢ(ξ(y))
(5.7): w·∇²g_r(y)w = −[A(y)w]·∇²_x L_r(ξ(y), y)⁻¹[A(y)w] − (1/2r) Σ_{i∉I} wᵢ². -/
theorem theorem_5_1_v
    {n m : ℕ} (X : Set (Pt n)) (hX : Convex ℝ X)
    (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (xbar : Pt n) (ybar : Mult m) (hA : Sec5Assumptions X f₀ f xbar ybar)
    (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ξ : Mult m → Pt n, ∀ y : Mult m,
      (⨆ y' : Mult m, gr X f₀ f r y') - gr X f₀ f r y ≤ (ε : EReal) →
      (ξ y ∈ X ∧ ∀ x ∈ X, x ≠ ξ y → Lr f₀ f r (ξ y) y < Lr f₀ f r x y) ∧
      (∀ z : Pt n, z ≠ 0 → 0 < hessForm (fun x' => Lr f₀ f r x' y) (ξ y) z) ∧
      gr X f₀ f r y ≠ ⊥ ∧ gr X f₀ f r y ≠ ⊤ ∧
      ContDiffAt ℝ 2 (grR X f₀ f r) y ∧
      (∀ w : Mult m, w ≠ 0 → hessForm (grR X f₀ f r) y w < 0) ∧
      ∀ w : Mult m, hessForm (grR X f₀ f r) y w =
        -(inner ℝ (∑ i ∈ activeSet f xbar, w i • gradient (f i) (ξ y))
            (ContinuousLinearMap.inverse (fderiv ℝ (gradient (fun x' => Lr f₀ f r x' y)) (ξ y))
              (∑ i ∈ activeSet f xbar, w i • gradient (f i) (ξ y))))
          - (1 / (2 * r)) * ∑ i ∈ (activeSet f xbar)ᶜ, w i ^ 2 := by sorry

end PenaltyLag.Rate
