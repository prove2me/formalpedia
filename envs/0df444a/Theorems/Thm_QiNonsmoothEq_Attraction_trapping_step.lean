-- Prove2me | Theorems.Thm_QiNonsmoothEq_Attraction_trapping_step
-- name    : QiNonsmoothEq.Attraction.trapping_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:25.059511+00:00
-- url     : https://prove2.me/theorems/c348d452-a82f-481c-8be7-dcb1cfaab926
-- title:
--   Proof of Theorem 5.1, p. 239 — the set N(x*, ε) = {‖x − x*‖ ≤ ε, ‖F(x)‖ ≤ ε/(2c + sp)} is invariant under one step
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^n$ be locally Lipschitz and B-differentiable at a zero $x^*$, and let $c$ satisfy $\|h\|\le c\|F'(x^*;h)\|$ for all $h$ (5.3). Let $x^{k+1}=x^k+\alpha_kd^k$ with $\alpha_k\ge 0$ and
--   $$\|F(x^{k+1})\|\le\|F(x^k)\| \tag{5.1}$$
--   for all $k$, and let $\delta_1,s,p>0$ be such that $\|x^k-x^*\|\le\delta_1$ implies $\alpha_k\le s$ and $\|d^k\|\le p\|F(x^k)\|$ (5.2). Then there is $\delta\in(0,\delta_1)$ such that for every $\epsilon\in(0,\delta)$ the set
--   $$N(x^*,\epsilon)=\Big\{x\in\mathbb R^n:\ \|x-x^*\|\le\epsilon,\ \|F(x)\|\le\frac{\epsilon}{2c+sp}\Big\}$$
--   is invariant under one step of the method: for every $k$, $x^k\in N(x^*,\epsilon)$ implies $x^{k+1}\in N(x^*,\epsilon)$.
--
--   Once an iterate enters $N(x^*,\epsilon)$, all later iterates stay there; since $x^*$ is a limiting point, every such set is entered, which gives convergence in Theorem 5.1.
--
--   **Formalization Note** The nonnegativity $\alpha_k\ge0$ is an added hypothesis (see Theorem 5.1): the page's step $\|x^k-x^*+\alpha_kd^k\|\le\|x^k-x^*\|+\alpha_k\|d^k\|$ uses it.
-- source:
--   Qi, Convergence analysis of some algorithms for solving nonsmooth equations, Math. Oper. Res. 18 (1993), p. 239, proof of Theorem 5.1, definition of N(x*, ε) and the display after it

import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_QiNonsmoothEq_Attraction_Setting
open Filter Topology NonsmoothNewton.Local

namespace QiNonsmoothEq.Attraction

/-- Qi 1993, proof of Theorem 5.1, p. 239: with `c` as in (5.3), there is `δ ∈ (0, δ₁)` such
that for every `ε ∈ (0, δ)` the set
`N(x*, ε) = {x : ‖x - x*‖ ≤ ε, ‖F(x)‖ ≤ ε / (2c + sp)}` is invariant under one step of the
descent direction method: `x^k ∈ N(x*, ε)` implies `x^{k+1} ∈ N(x*, ε)`. -/
theorem trapping_step {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (xstar : EuclideanSpace ℝ (Fin n)) (hBx : QiNonsmoothEq.Local.BDiffAt F xstar) (hzero : F xstar = 0)
    (c : ℝ) (hc : ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ c * ‖dirDeriv F xstar h‖)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ)
    (hstep : ∀ k, x (k + 1) = x k + α k • d k) (hα : ∀ k, 0 ≤ α k)
    (hdesc : ∀ k, ‖F (x (k + 1))‖ ≤ ‖F (x k)‖)
    (δ₁ s p : ℝ) (hδ₁ : 0 < δ₁) (hs : 0 < s) (hp : 0 < p)
    (hloc : ∀ k, ‖x k - xstar‖ ≤ δ₁ → α k ≤ s ∧ ‖d k‖ ≤ p * ‖F (x k)‖) :
    ∃ δ : ℝ, 0 < δ ∧ δ < δ₁ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ k : ℕ,
      (‖x k - xstar‖ ≤ ε ∧ ‖F (x k)‖ ≤ ε / (2 * c + s * p)) →
      (‖x (k + 1) - xstar‖ ≤ ε ∧ ‖F (x (k + 1))‖ ≤ ε / (2 * c + s * p)) := by sorry

end QiNonsmoothEq.Attraction
