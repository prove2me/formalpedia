-- Prove2me | Theorems.Thm_RWPI_Classif_logistic_inner_sup
-- name    : RWPI.Classif.logistic_inner_sup
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:52:51.659187+00:00
-- url     : https://prove2.me/theorems/75580cb0-c7f0-447e-830b-073ccd64cae9
-- title:
--   Proof of Theorem 2, p. 30 — the inner supremum for the logistic loss
-- statement:
--   Let $p, q \in [1,\infty]$ satisfy $1/p + 1/q = 1$. Let $\beta, x_0 \in \mathbb R^d$, let $y_0 \in \{-1,+1\}$ and let $\lambda \ge 0$. Then
--
--   $$\sup_{x \in \mathbb R^d}\Big\{ \log\big(1 + \exp(-y_0\,\beta^T x)\big) - \lambda\,\|x - x_0\|_q \Big\} = \begin{cases} \log\big(1 + \exp(-y_0\,\beta^T x_0)\big) & \text{if } \|\beta\|_p \le \lambda,\\ +\infty & \text{if } \|\beta\|_p > \lambda.\end{cases}$$
--
--   This is the value of the dual integrand $\varphi_\lambda(x_0,y_0)$ of Proposition 1 for the logistic loss under the label-preserving cost $N_q$, once the response is held at $y_0$. It is the step of the proof of Theorem 2 that produces the penalty $\|\beta\|_p$.
--
--   **Formalization Note** The display in the paper writes the transport norm as $\|\cdot\|_p$ and the threshold as $\|\beta\|_q$; since $p$ and $q$ are conjugate the display holds either way, and the statement here uses Theorem 2's convention (transport norm $\ell_q$, regularizer $\ell_p$). The supremum is taken in $[0,\infty]$ with truncated subtraction, which does not change its value because the term at $x = x_0$ is already at least every truncated term.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, App. A.1, proof of Theorem 2, p. 30 (second display, following Lemma 1 of Shafieezadeh-Abadeh et al. 2015)

import Mathlib
import Definitions.Def_RWPI_Classif_losses

open scoped ENNReal

namespace RWPI.Classif

/-- App. A.1, proof of Theorem 2, p. 30 ("following Lemma 1 in [42]"): for a label
`y₀ ∈ {−1, +1}`, a point `x₀ ∈ ℝ^d` and `λ ≥ 0`,
`sup_x { log(1 + exp(−y₀ βᵀx)) − λ ‖x − x₀‖_q } = log(1 + exp(−y₀ βᵀx₀))` if `‖β‖_p ≤ λ`
and `+∞` otherwise, where `1/p + 1/q = 1`. Stated in Theorem 2's convention (transport norm
`ℓ_q`, regularizer `ℓ_p`); the proof's display has the two exponents swapped. -/
theorem logistic_inner_sup {d : ℕ} (p q : ℝ≥0∞) (hpq : p.HolderConjugate q)
    (β x₀ : Fin d → ℝ) (y₀ : ℝ) (hy₀ : y₀ = 1 ∨ y₀ = -1) (lam : ℝ) (hlam : 0 ≤ lam) :
    (⨆ x : Fin d → ℝ, (ENNReal.ofReal (logLoss β (x, y₀)) -
        ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q (x - x₀)‖)) =
      if ‖WithLp.toLp p β‖ ≤ lam then ENNReal.ofReal (logLoss β (x₀, y₀)) else ⊤ := by sorry

end RWPI.Classif
