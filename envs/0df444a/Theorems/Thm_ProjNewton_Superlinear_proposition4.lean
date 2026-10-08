-- Prove2me | Theorems.Thm_ProjNewton_Superlinear_proposition4
-- name    : ProjNewton.Superlinear.proposition4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:31:27.859149+00:00
-- url     : https://prove2.me/theorems/ad876e93-11b2-4eb0-81ac-3a8f1652ffcd
-- title:
--   Proposition 4 — superlinear convergence of the projected Newton method
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and twice continuously differentiable. Suppose problem (1) has a unique optimal solution $x^*$ in the nonnegative orthant satisfying Assumption (C). Suppose also that some $0<m_1,m_2$ bound the Hessian quadratic form at every point $y$ in the unrestricted initial level set $\{y:f(y)\le f(x_0)\}$ and in every direction $z$:
--
--   $$m_1\|z\|^2\le z^\top\nabla^2f(y)z\le m_2\|z\|^2.$$
--
--   Run (32)–(37) with $D_k=H_k^{-1}$, where $H_k$ zeros only off-diagonal Hessian entries touching $I_k^+$. Then $x_k\to x^*$ and the error converges superlinearly: for every $c>0$, eventually $\|x_{k+1}-x^*\|\le c\|x_k-x^*\|$. If the Hessian is Lipschitz on a neighborhood of $x^*$, the error is at least quadratic: for some $C>0$, eventually $\|x_{k+1}-x^*\|\le C\|x_k-x^*\|^2$.
--
--   This is the paper's main rate claim for its partly diagonal projected Newton method.
--
--   **Formalization Note** The printed bound misbinds $z$ in the level set while leaving its Hessian point free; it is read as the stated $y,z$ quantification. The level set has no feasibility restriction, as printed. The $C^2$ hypothesis includes the standing $C^1$ convention; $x^*$ is feasible and uniquely optimal among feasible points. The run starts feasible and chooses the first acceptable exponent. No convergence, matrix invertibility, active-set identification or admissibility is assumed. Superlinearity uses a uniform eventual inequality, so finite termination is covered.
-- source:
--   Bertsekas, Projected Newton Methods for Optimization Problems with Simple Constraints, SIAM J. Control Optim. 20(2) (1982), p. 236, Proposition 4; Assumption (C), p. 233

import Mathlib
import Definitions.Def_ProjNewton_Superlinear_Algorithm

namespace ProjNewton.Superlinear

open Matrix Filter Topology

/-- Bertsekas (1982), Proposition 4, p. 236. -/
theorem proposition4 {n : ℕ} (hn : 0 < n) (f : Vec n → ℝ)
    (hf2 : ContDiff ℝ 2 f) (hconv : ConvexOn ℝ Set.univ f)
    (xs : Vec n) (hopt : xs ∈ orthant n ∧ ∀ y ∈ orthant n, f xs ≤ f y)
    (huniq : ∀ y ∈ orthant n, (∀ z ∈ orthant n, f y ≤ f z) → y = xs)
    (hC : AssumptionC f xs) (μ : Fin n → ℝ) (ε β σ : ℝ)
    (hpar : Params μ ε β σ) (x : ℕ → Vec n)
    (hm : ∃ m₁ m₂ : ℝ, 0 < m₁ ∧ 0 < m₂ ∧
      ∀ y : Vec n, f y ≤ f (x 0) → ∀ z : Fin n → ℝ,
        m₁ * (z ⬝ᵥ z) ≤ hessForm f y z ∧ hessForm f y z ≤ m₂ * (z ⬝ᵥ z))
    (hrun : IsRun f μ ε β σ (fun k => (Hmat f μ ε (x k))⁻¹) x) :
    Tendsto x atTop (𝓝 xs) ∧
    (∀ c : ℝ, 0 < c → ∀ᶠ k in atTop,
      ‖x (k + 1) - xs‖ ≤ c * ‖x k - xs‖) ∧
    ((∃ δ : ℝ, 0 < δ ∧ ∃ L : NNReal,
      LipschitzOnWith L (fderiv ℝ (gradient f)) (Metric.ball xs δ)) →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop,
        ‖x (k + 1) - xs‖ ≤ C * ‖x k - xs‖ ^ 2) := by sorry

end ProjNewton.Superlinear
