-- Prove2me | Theorems.Thm_StochQuasiNewton_SQN_expected_descent
-- name    : StochQuasiNewton.SQN.expected_descent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:37:54.919984+00:00
-- url     : https://prove2.me/theorems/c90baeb1-3878-49ca-9a8a-3e9da198f2f6
-- title:
--   Eq. (3.18) — expected descent of the Newton-like iteration
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R$ be $C^2$ with $\lambda I\prec\nabla^2F(w)\prec\Lambda I$ for all $w$ (3.4), $0<\lambda,\Lambda$. Let $w^k,\xi^k,H_k$ be a Newton-like iteration (3.14) with step lengths $\alpha^k>0$, constants $0<\mu_1\le\mu_2$ and $\gamma$ (see the definition `NewtonLikeIteration`). Then for every $k\ge1$, $F(w^{k+1})$ is integrable and, almost surely,
--   $$E\big[F(w^{k+1})\,\big|\,\mathcal F_k\big]\le F(w^k)-\alpha^k\mu_1\|\nabla F(w^k)\|^2+\frac\Lambda2(\alpha^k\mu_2)^2\gamma^2 .$$
--
--   This is the one-step descent inequality that drives the convergence analysis of Theorem 3.2.
--
--   **Formalization Note** The paper's $E_{\xi^k}[\cdot]$ (expectation over $\xi^k$ with $w^k$ fixed) is the conditional expectation given $\mathcal F_k$. The first line of (3.18) on the page has the typo $E_{\xi^k}[\|\nabla f(w^k,\xi^k)\|]^2$ for $E_{\xi^k}[\|\nabla f(w^k,\xi^k)\|^2]$; only the final inequality is stated.
-- source:
--   Byrd, Hansen, Nocedal, Singer, A Stochastic Quasi-Newton Method for Large-Scale Optimization, SIAM J. Optim. 26(2) (2016), p. 1017, Eq. (3.18)

import Mathlib
import Definitions.Def_StochQuasiNewton_SQN_FiniteSum
import Definitions.Def_StochQuasiNewton_SQN_NewtonLike

open scoped RealInnerProductSpace
open MeasureTheory

namespace StochQuasiNewton.SQN

/-- Eq. (3.18): for the Newton-like iteration (3.14) on a `C²` objective `F` with
`λ I ≺ ∇²F(w) ≺ Λ I` (3.4), step lengths `α^k > 0`, and the conditions of `NewtonLikeIteration`,
for every `k ≥ 1`, `F(w^{k+1})` is integrable and, almost surely,
`E[F(w^{k+1}) | ℱ_k] ≤ F(w^k) − α^k μ₁ ‖∇F(w^k)‖² + (Λ/2)(α^k μ₂)² γ²`. -/
theorem expected_descent {n : ℕ} {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 2 F) (lam Lam : ℝ) (hlam : 0 < lam)
    (hLam : 0 < Lam)
    (hHess : ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (fderiv ℝ (gradient F) w))
    (G : EuclideanSpace ℝ (Fin n) → Ξ → EuclideanSpace ℝ (Fin n)) (γ : ℝ) (α : ℕ → ℝ)
    (hα : ∀ k, 1 ≤ k → 0 < α k) (μ₁ μ₂ : ℝ) (hμ₁ : 0 < μ₁) (hμ : μ₁ ≤ μ₂)
    (w1 : EuclideanSpace ℝ (Fin n)) (w : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ξ : ℕ → Ω → Ξ)
    (H : ℕ → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hrun : NewtonLikeIteration P ℱ F G γ α μ₁ μ₂ w1 w ξ H) (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun ω => F (w (k + 1) ω)) P ∧
      P[fun ω => F (w (k + 1) ω) | ℱ k] ≤ᵐ[P] fun ω =>
        F (w k ω) - α k * μ₁ * ‖gradient F (w k ω)‖ ^ 2 + Lam / 2 * (α k * μ₂) ^ 2 * γ ^ 2 := by sorry

end StochQuasiNewton.SQN
