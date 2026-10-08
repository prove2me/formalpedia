-- Prove2me | Theorems.Thm_RWPI_Classif_hinge_inner_sup
-- name    : RWPI.Classif.hinge_inner_sup
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:53:16.02774+00:00
-- url     : https://prove2.me/theorems/550f984b-8904-416d-a498-504d95a8fd35
-- title:
--   Proof of Theorem 2, pp. 30–31 — the inner supremum for the hinge loss
-- statement:
--   Let $p, q \in [1,\infty]$ satisfy $1/p + 1/q = 1$. Let $\beta, x_0 \in \mathbb R^d$, let $y_0 \in \{-1,+1\}$ and let $\lambda \ge 0$. Then
--
--   $$\sup_{\Delta \in \mathbb R^d}\Big\{ \big(1 - y_0\,\beta^T(x_0 + \Delta)\big)^+ - \lambda\,\|\Delta\|_q \Big\} = \begin{cases} \big(1 - y_0\,\beta^T x_0\big)^+ & \text{if } \|\beta\|_p \le \lambda,\\ +\infty & \text{if } \|\beta\|_p > \lambda.\end{cases}$$
--
--   This is the dual integrand of Proposition 1 for the hinge loss under the label-preserving cost $N_q$, written in the displacement $\Delta = x - x_0$. It is the step of the proof of Theorem 2 that produces the penalty $\|\beta\|_p$ for the support vector machine.
--
--   **Formalization Note** The paper's display writes the transport norm as $\|\cdot\|_p$ and the threshold as $\|\beta\|_q$ (the reverse of Theorem 2's statement; both readings are true since $p, q$ are conjugate); the statement uses Theorem 2's convention. Typographical artefacts of the page (the index $\Delta u_i$ for $\Delta_i$, a stray $+\infty$ in the first case) are not reproduced. The supremum is taken in $[0,\infty]$ with truncated subtraction, harmless because the term at $\Delta = 0$ dominates every truncated term.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, App. A.1, proof of Theorem 2, pp. 30–31 (display after 'For each i, let us consider the maximization problem')

import Mathlib
import Definitions.Def_RWPI_Classif_losses

open scoped ENNReal

namespace RWPI.Classif

/-- App. A.1, proof of Theorem 2, pp. 30–31: for a label `y₀ ∈ {−1, +1}`, a point `x₀ ∈ ℝ^d`
and `λ ≥ 0`, `sup_Δ { (1 − y₀ βᵀ(x₀ + Δ))⁺ − λ ‖Δ‖_q } = (1 − y₀ βᵀx₀)⁺` if `‖β‖_p ≤ λ` and
`+∞` otherwise, where `1/p + 1/q = 1`. Stated in Theorem 2's convention (transport norm `ℓ_q`,
regularizer `ℓ_p`); the proof's display has the two exponents swapped. -/
theorem hinge_inner_sup {d : ℕ} (p q : ℝ≥0∞) (hpq : p.HolderConjugate q)
    (β x₀ : Fin d → ℝ) (y₀ : ℝ) (hy₀ : y₀ = 1 ∨ y₀ = -1) (lam : ℝ) (hlam : 0 ≤ lam) :
    (⨆ Δ : Fin d → ℝ, (ENNReal.ofReal (hingeLoss β (x₀ + Δ, y₀)) -
        ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q Δ‖)) =
      if ‖WithLp.toLp p β‖ ≤ lam then ENNReal.ofReal (hingeLoss β (x₀, y₀)) else ⊤ := by sorry

end RWPI.Classif
