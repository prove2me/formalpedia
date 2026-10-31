-- Prove2me | Theorems.Thm_TRSHolderKL_lemma_3_7
-- name    : TRSHolderKL.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:49.195539+00:00
-- url     : https://prove2.me/theorems/86ab8ccc-8191-4942-8bb7-c3c1bd184daa
-- title:
--   Lemma 3.7 — error bounds when $\lambda_1\ge0$ and $\min_{\mathbb R^n}f=f^*$
-- statement:
--   Let $A$ be a nonzero real symmetric $n\times n$ matrix ($n\ge2$) with smallest eigenvalue $\lambda_1\ge0$, $b\in\mathbb R^n$, assume $\min_{x\in\mathbb R^n}f(x)=f^*$, and let $\tilde x=A^\dagger b$. Then:
--   1. if $\lambda_1>0$, then for all $x\in\mathbb R^n$
--   $$
--   \operatorname{dist}(x,S_0)\le\sqrt{1/\lambda_1}\,\big[f(x)-f^*+\delta_B(x)\big]^{1/2};
--   $$
--   2. if $\lambda_1=0$ and $\|\tilde x\|=1$, then $S_0=\{\tilde x\}$ and there is $\tau>0$ with $\operatorname{dist}(x,S_0)\le\tau[f(x)-f^*+\delta_B(x)]^{1/4}$ for all $x$;
--   3. if $\lambda_1=0$ and $\|\tilde x\|<1$, then there is $\tau>0$ with $\operatorname{dist}(x,S_0)\le\tau[f(x)-f^*+\delta_B(x)]^{1/2}$ for all $x$.
--
--   Case 2 is the convex instance of the TRS-ill case, the only convex situation in which the modulus drops to $1/4$.
--
--   Differences from the source:
--   - encoding: ℝⁿ; an n × n nonzero real symmetric matrix A; λ₁ the smallest eigenvalue → EuclideanSpace ℝ (Fin n); A : Matrix with A.IsHermitian and A ≠ 0 acting by Matrix.toEuclideanLin; lam1 A the least element of the real spectrum; reason: Lean conventions; the same instances
--   - encoding: for all x ∈ ℝⁿ, with δ_B(x) inside the right-hand side → for all x with ‖x‖ ≤ 1, δ_B dropped; reason: for ‖x‖ > 1 the paper's right-hand side is +∞ (δ_B = +∞), so the inequality is trivial there; on the ball δ_B = 0
--   - encoding: min_{x∈ℝⁿ} f(x) = f* → ∀ y, f* ≤ f y; reason: f* is attained on the ball, so the global minimum equals f* exactly when f* is a global lower bound
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Lemma 3.7, p.6

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_f
import Definitions.Def_TRSHolderKL_fstar
import Definitions.Def_TRSHolderKL_S0
import Definitions.Def_TRSHolderKL_lam1
import Definitions.Def_TRSHolderKL_xtilde

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

/-- Lemma 3.7, Jiang and Li, arXiv:1911.11955v2, p.6. Assume `λ₁ ≥ 0` and
`min_{x ∈ ℝⁿ} f(x) = f*`, and let `x̃ = A†b`. Then
1. if `λ₁ > 0`, `dist(x, S₀) ≤ √(1/λ₁) [f(x) − f* + δ_B(x)]^{1/2}` for all `x`;
2. if `λ₁ = 0` and `‖x̃‖ = 1`, then `S₀ = {x̃}` and for some `τ > 0`,
   `dist(x, S₀) ≤ τ [f(x) − f* + δ_B(x)]^{1/4}` for all `x`;
3. if `λ₁ = 0` and `‖x̃‖ < 1`, then for some `τ > 0`,
   `dist(x, S₀) ≤ τ [f(x) − f* + δ_B(x)]^{1/2}` for all `x`.

**Formalization Note.** `min_{ℝⁿ} f = f*` is `∀ y, f* ≤ f y` (with `f*` attained on the
ball). The inequalities are stated for `‖x‖ ≤ 1`, where `δ_B(x) = 0`; outside `B` the right
sides are `+∞`. -/
theorem lemma_3_7 {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA0 : A ≠ 0) (b : E n) (hlam : 0 ≤ lam1 A) (hmin : ∀ y : E n, fstar A b ≤ f A b y) :
    (0 < lam1 A → ∀ x : E n, ‖x‖ ≤ 1 →
      Metric.infDist x (S0 A b) ≤
        Real.sqrt (1 / lam1 A) * (f A b x - fstar A b) ^ ((1 : ℝ) / 2)) ∧
    (lam1 A = 0 → ‖xtilde A b‖ = 1 →
      S0 A b = {xtilde A b} ∧
      ∃ τ : ℝ, 0 < τ ∧ ∀ x : E n, ‖x‖ ≤ 1 →
        Metric.infDist x (S0 A b) ≤ τ * (f A b x - fstar A b) ^ ((1 : ℝ) / 4)) ∧
    (lam1 A = 0 → ‖xtilde A b‖ < 1 →
      ∃ τ : ℝ, 0 < τ ∧ ∀ x : E n, ‖x‖ ≤ 1 →
        Metric.infDist x (S0 A b) ≤ τ * (f A b x - fstar A b) ^ ((1 : ℝ) / 2)) := by sorry

end TRSHolderKL
