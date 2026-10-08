-- Prove2me | Theorems.Thm_SAG_SmallStep_lyapunov_dominates
-- name    : SAG.SmallStep.lyapunov_dominates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:26:39.676475+00:00
-- url     : https://prove2.me/theorems/0b81e1c2-7a6b-498f-8125-79c46f4b5af8
-- title:
--   §A.5 Step 2, pp. 22–23 — $Q(\theta)\ge\frac13\|x-x^*\|^2$
-- statement:
--   Let $n\ge1$, let $f'_1,\dots,f'_n:\mathbb R^p\to\mathbb R^p$, $x^*\in\mathbb R^p$ and $\alpha>0$, and let $Q$ be the Lyapunov function of §A.5 with step size $\alpha$. Then for every SAG state $\theta=(y,x)$,
--   $$
--   Q(\theta)\ge\frac13\|x-x^*\|^2 .
--   $$
--   Equivalently, $P-\begin{pmatrix}0&0\\0&\frac13I\end{pmatrix}$ is positive semidefinite.
--
--   This domination converts the linear convergence of $\mathbb EQ(\theta^k)$ into the convergence of $\mathbb E\|x^k-x^*\|^2$ in Proposition 1.
--
--   **Formalization Note** The page shows it for $\alpha=\frac1{2nL}$ and writes "≻ 0 for $n\geqslant2$" at the end of its Schur-complement computation; its exact expression $\frac23I-\frac{n(1-1/n)^2}{3n+1/n-2}\frac{ee^\top}{n}$ is positive definite for every $n\ge1$, and neither it nor the claim depends on the value of $\alpha>0$. The statement is therefore made for every $n\ge1$ and every $\alpha>0$. No hypothesis on $f'$ or $x^*$ is needed.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, pp. 22–23, §A.5 Step 2

import Mathlib
import Definitions.Def_SAG_SmallStep_blockForm
import Definitions.Def_SAG_SmallStep_lyapunov

namespace SAG.SmallStep

/-- §A.5 Step 2 (arXiv:1202.6258v4, pp. 22–23): the Lyapunov function of §A.5 dominates
`⅓‖x − x*‖²`, `Q(θ) ≥ ⅓‖x − x*‖²` for every state `θ = (y, x)` and every step size `α > 0`. -/
theorem lyapunov_dominates {p n : ℕ} (hn : 0 < n)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (xstar : EuclideanSpace ℝ (Fin p)) (α : ℝ) (hα : 0 < α)
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    (1 / 3) * ‖θ.2 - xstar‖ ^ 2 ≤ lyapunov f' α xstar θ := by sorry

end SAG.SmallStep
