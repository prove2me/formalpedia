-- Prove2me | Theorems.Thm_RiskyBenefitCost_NthDegree_display_7
-- name    : RiskyBenefitCost.NthDegree.display_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:19.150622+00:00
-- url     : https://prove2.me/theorems/d9332c57-3e2c-40cb-a63e-02d2ddde8e1d
-- title:
--   Display (7), p. 3628 (PDF 5), in φ = f(b) — derivative of the sign-adjusted Nth derivative (5)
-- statement:
--   Let $N\ge1$ and let $U:\mathbb R\to\mathbb R$ be $(N+1)$ times continuously differentiable. Fix constants $x_0,z_0,X$ and write $w(\varphi)=\varphi\,(X-x_0)+z_0$. Then the function
--   $$g(\varphi)=(-1)^N\varphi^N\,U^{(N)}\big(w(\varphi)\big)$$
--   is differentiable at every $\varphi\in\mathbb R$ with
--   $$g'(\varphi)=\varphi^{N-1}\Big[\varphi\,(X-x_0)\,(-1)^{N+2}U^{(N+1)}\big(w(\varphi)\big)-N(-1)^{N+1}U^{(N)}\big(w(\varphi)\big)\Big].$$
--
--   With $\varphi=f(b)$, $g(f(b))$ is the quantity (5), and for differentiable $f$ the paper's display (7) is $f'(b)\,g'(f(b))$. The sign of the bracket, display (8), decides whether (5) increases or decreases in $b$.
--
--   **Formalization Note.** The paper differentiates in $b$ and so carries the chain-rule factor $f'(b)$, which presupposes differentiable $f$. Proposition 2 assumes only continuity of $f$, so the identity is stated in the variable $\varphi=f(b)$; it is the paper's (7) without the factor $f'(b)$. The bracket is written with $U^{(N)}$, not with $r_{N+1}$, so that it holds also where $U^{(N)}$ vanishes.
-- source:
--   Menegatti & Peter, Changes in risky benefits and in risky costs: a question of the right order, Management Science 68(5) (2022), p. 3628 (PDF 5), display (7) (restated in φ = f(b))

import Mathlib
import Definitions.Def_RiskyBenefitCost_NthDegree_Model

namespace RiskyBenefitCost.NthDegree

theorem display_7 (N : ℕ) (hN : 1 ≤ N) (U : ℝ → ℝ) (hU : ContDiff ℝ (N + 1) U)
    (x0 z0 X φ : ℝ) :
    HasDerivAt (fun φ : ℝ => (-1 : ℝ) ^ N * φ ^ N * iteratedDeriv N U (φ * (X - x0) + z0))
      (φ ^ (N - 1) *
        (φ * (X - x0) * (-1 : ℝ) ^ (N + 2) * iteratedDeriv (N + 1) U (φ * (X - x0) + z0)
          - N * (-1 : ℝ) ^ (N + 1) * iteratedDeriv N U (φ * (X - x0) + z0))) φ := by sorry

end RiskyBenefitCost.NthDegree
