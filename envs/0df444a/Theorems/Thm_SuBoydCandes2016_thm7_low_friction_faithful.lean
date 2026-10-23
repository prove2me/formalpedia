-- Prove2me | Theorems.Thm_SuBoydCandes2016_thm7_low_friction_faithful
-- name    : SuBoydCandes2016.thm7_low_friction_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T00:28:07.807585+00:00
-- url     : https://prove2.me/theorems/8f083f00-6d83-4c17-85bb-151b9fc24888
-- title:
--   Theorem 7, p. 16: inverse-quadratic rate for 1 < r < 3 under convexity of (f − f⋆)^((r−1)/2)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and continuously differentiable, let $x^\star$ be a minimizer of $f$ and $f^\star=f(x^\star)$, and let $1<r<3$. Let $X\in C^2((0,\infty);\mathbb R^n)\cap C^1([0,\infty);\mathbb R^n)$ solve
--
--   $$\ddot X+\frac rt\dot X+\nabla f(X)=0,\qquad X(0)=x_0,\ \dot X(0)=0.$$
--
--   If $(f-f^\star)^{(r-1)/2}$ is convex, then
--
--   $$f(X(t))-f^\star\le\frac{(r-1)^2\|x_0-x^\star\|^2}{2t^2}\qquad\text{for all }t>0.$$
--
--   This is Theorem 7 of Su, Boyd and Candès: below the friction threshold $r=3$, the inverse-quadratic rate of Theorem 5 survives under an extra convexity condition on a power of $f-f^\star$.
--
--   **Formalization Note** A solution is encoded as a pair $(X,V)$ with $V=\dot X$ on $(0,\infty)$ and right-hand regularity at $0$; the statement ranges over every such solution. No Lipschitz condition on $\nabla f$ is assumed, as in the paper.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method: Theory and Insights, JMLR 17 (2016), arXiv:1503.01243v2, https://arxiv.org/abs/1503.01243, p. 16, Theorem 7

import Mathlib
import Definitions.Def_NesterovODE_StrongCvx_Setting

theorem SuBoydCandes2016.thm7_low_friction_faithful {n : ℕ} (f : NesterovODE.WellPosed.E n → ℝ) (r : ℝ)
    (hr1 : 1 < r) (hr3 : r < 3)
    (hfc : ConvexOn ℝ Set.univ f) (hfd : ContDiff ℝ 1 f)
    (x₀ xstar : NesterovODE.WellPosed.E n) (hxstar : ∀ y, f xstar ≤ f y)
    (hpow : ConvexOn ℝ Set.univ (fun x => (f x - f xstar) ^ ((r - 1) / 2)))
    (X V : ℝ → NesterovODE.WellPosed.E n) (hX : NesterovODE.StrongCvx.IsSolution f r x₀ X V) :
    ∀ t : ℝ, 0 < t → f (X t) - f xstar ≤ (r - 1) ^ 2 * ‖x₀ - xstar‖ ^ 2 / (2 * t ^ 2) := by sorry
