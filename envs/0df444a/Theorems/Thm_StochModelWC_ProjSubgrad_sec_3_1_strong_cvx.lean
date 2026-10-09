-- Prove2me | Theorems.Thm_StochModelWC_ProjSubgrad_sec_3_1_strong_cvx
-- name    : StochModelWC.ProjSubgrad.sec_3_1_strong_cvx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:34:16.744399+00:00
-- url     : https://prove2.me/theorems/2a614be9-c658-49a3-9c51-71746e513aa5
-- title:
--   §3.1, display after (3.8) — f(x) − f(x̂) − ρ/2‖x − x̂‖² ≥ (ρ̄ − ρ)‖x − x̂‖² = (ρ̄ − ρ)/ρ̄² ‖∇φ_{1/ρ̄}(x)‖²
-- statement:
--   Let $X \subseteq \mathbb R^d$ be nonempty, closed and convex, let $f : \mathbb R^d \to \mathbb R$ be $\rho$-weakly convex with $\rho > 0$, and let $\varphi = f + \delta_X$, where $\delta_X$ is the indicator of $X$. Fix $\bar\rho > \rho$, a point $x \in X$, and let
--   $$\hat x = \operatorname{prox}_{\varphi/\bar\rho}(x) \in \operatorname*{argmin}_{y \in X}\Big\{f(y) + \frac{\bar\rho}{2}\|y - x\|^2\Big\}.$$
--   Then
--   $$f(x) - f(\hat x) - \frac{\rho}{2}\|x - \hat x\|^2 \;\ge\; (\bar\rho - \rho)\|x - \hat x\|^2 \;=\; \frac{\bar\rho - \rho}{\bar\rho^2}\,\|\nabla\varphi_{1/\bar\rho}(x)\|^2,$$
--   where $\varphi_{1/\bar\rho}(x) = \min_{y \in X}\{f(y) + \frac{\bar\rho}{2}\|y - x\|^2\}$ is the Moreau envelope.
--
--   In the proof of Theorem 3.1 this is the step that converts the descent of the Moreau envelope along one iteration of the projected stochastic subgradient method into the stationarity measure $\|\nabla\varphi_{1/\bar\rho}\|^2$. The inequality comes from strong convexity, with parameter $\bar\rho - \rho$, of $y \mapsto f(y) + \frac{\bar\rho}{2}\|y - x\|^2$ on $X$; the equality from the gradient formula of Lemma 2.2.
--
--   **Formalization Note.** $\hat x$ is any minimizer over $X$ (it is unique). The gradient is Mathlib's `gradient`, which equals the Fréchet gradient wherever the envelope is differentiable; by Lemma 2.2 it is differentiable everywhere here, since $1/\bar\rho < 1/\rho$.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, pp. 13–14, §3.1, proof of Theorem 3.1, display after (3.8)

import Mathlib
import Definitions.Def_StochModelWC_ProjSubgrad_Basic

open MeasureTheory Filter Topology

namespace StochModelWC.ProjSubgrad

/-- §3.1, display after (3.8) (pp. 13–14): for `φ = f + δ_X` with `f` `ρ`-weakly convex and `X` closed, convex and
nonempty, `ρ̄ > ρ`, `x ∈ X` and `x̂ = prox_{φ/ρ̄}(x)` (a minimizer over `X` of `f(y) + ρ̄/2‖y − x‖²`),
`f(x) − f(x̂) − ρ/2‖x − x̂‖² ≥ (ρ̄ − ρ)‖x − x̂‖² = (ρ̄ − ρ)/ρ̄² · ‖∇φ_{1/ρ̄}(x)‖²`. -/
theorem sec_3_1_strong_cvx {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (ρ ρbar : ℝ) (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X) (hX_ne : X.Nonempty)
    (hf : IsWeaklyConvexOn Set.univ ρ f) (hρ : 0 < ρ) (hρbar : ρ < ρbar)
    (x xhat : EuclideanSpace ℝ (Fin d)) (hx : x ∈ X) (hxhat : IsProxPt X f (1 / ρbar) x xhat) :
    (ρbar - ρ) * ‖x - xhat‖ ^ 2 ≤ f x - f xhat - ρ / 2 * ‖x - xhat‖ ^ 2 ∧
    (ρbar - ρ) * ‖x - xhat‖ ^ 2 =
      (ρbar - ρ) / ρbar ^ 2 * ‖gradient (moreauEnv X f (1 / ρbar)) x‖ ^ 2 := by sorry

end StochModelWC.ProjSubgrad
