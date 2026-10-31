-- Prove2me | Theorems.Thm_TRSHolderKL_lemma_3_6
-- name    : TRSHolderKL.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:04.798989+00:00
-- url     : https://prove2.me/theorems/5c4cf7d8-9d08-4398-ad68-a549d59b3487
-- title:
--   Lemma 3.6 — error bound with modulus 1/2 when $\lambda_1\ge0$ and $\min_{\mathbb R^n}f<f^*$
-- statement:
--   Let $A$ be a nonzero real symmetric $n\times n$ matrix ($n\ge2$) with smallest eigenvalue $\lambda_1\ge0$, $b\in\mathbb R^n$, and assume $\inf_{x\in\mathbb R^n}f(x)<f^*$. Then there is $\tau>0$ such that
--   $$
--   \operatorname{dist}(x,S_0)\le\tau\big(f(x)-f^*+\delta_B(x)\big)^{1/2}\qquad\text{for all }x\in\mathbb R^n,
--   $$
--   where $\delta_B$ is the indicator of the unit ball.
--
--   This is the convex TRS whose minimizer is forced onto the boundary of the ball; the error bound has the quadratic-growth modulus $1/2$.
--
--   Differences from the source:
--   - encoding: ℝⁿ; an n × n nonzero real symmetric matrix A; λ₁ the smallest eigenvalue → EuclideanSpace ℝ (Fin n); A : Matrix with A.IsHermitian and A ≠ 0 acting by Matrix.toEuclideanLin; lam1 A the least element of the real spectrum; reason: Lean conventions; the same instances
--   - encoding: for all x ∈ ℝⁿ, with δ_B(x) inside the right-hand side → for all x with ‖x‖ ≤ 1, δ_B dropped; reason: for ‖x‖ > 1 the paper's right-hand side is +∞ (δ_B = +∞), so the inequality is trivial there; on the ball δ_B = 0
--   - encoding: min_{x∈ℝⁿ} f(x) < f* (the minimum may be −∞) → ∃ y, f y < f*; reason: the same condition, with no need to define the possibly infinite minimum
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Lemma 3.6, display (4), p.5

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_f
import Definitions.Def_TRSHolderKL_fstar
import Definitions.Def_TRSHolderKL_S0
import Definitions.Def_TRSHolderKL_lam1

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

/-- Lemma 3.6, Jiang and Li, arXiv:1911.11955v2, display (4), p.5. Assume `λ₁ ≥ 0` and
`min_{x ∈ ℝⁿ} f(x) < f*`. Then there is `τ > 0` with
`dist(x, S₀) ≤ τ (f(x) − f* + δ_B(x))^{1/2}` for all `x ∈ ℝⁿ`.

**Formalization Note.** `min_{ℝⁿ} f < f*` (the minimum may be `−∞`) is `∃ y, f y < f*`. The
inequality is stated for `‖x‖ ≤ 1` with `δ_B(x) = 0`; for `‖x‖ > 1` the right side is `+∞`. -/
theorem lemma_3_6 {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA0 : A ≠ 0) (b : E n) (hlam : 0 ≤ lam1 A) (hmin : ∃ y : E n, f A b y < fstar A b) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ x : E n, ‖x‖ ≤ 1 →
      Metric.infDist x (S0 A b) ≤ τ * (f A b x - fstar A b) ^ ((1 : ℝ) / 2) := by sorry

end TRSHolderKL
