-- Prove2me | Theorems.Thm_StochQuasiNewton_SQN_suboptimality_le_gradient_sq
-- name    : StochQuasiNewton.SQN.suboptimality_le_gradient_sq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:38:39.029984+00:00
-- url     : https://prove2.me/theorems/7fb31e53-3213-496e-8acb-14b3c910961c
-- title:
--   Eq. (3.19) — suboptimality bounded by the squared gradient norm
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R$ be $C^2$ and suppose $\nabla^2F(w)\succ\lambda I$ for every $w$, with $\lambda>0$ (the lower bound in (3.4)). Then for all $v,w\in\mathbb R^n$,
--   $$F(v)\ge F(w)-\frac1{2\lambda}\|\nabla F(w)\|^2,$$
--   and if $w^*$ minimizes $F$, then for every $w$
--   $$2\lambda\,[F(w)-F(w^*)]\le\|\nabla F(w)\|^2 .$$
--
--   This inequality converts the gradient term of the descent inequality (3.18) into a suboptimality term, yielding the recursion (3.22).
--
--   **Formalization Note** Only the lower Hessian bound is assumed, as in the paper's derivation. A published Boyd–Vandenberghe statement of the same inequality exists on the platform in the older Mathlib environment `c5ea003`; it cannot be imported from this mission's environment, so the inequality is restated here.
-- source:
--   Byrd, Hansen, Nocedal, Singer, A Stochastic Quasi-Newton Method for Large-Scale Optimization, SIAM J. Optim. 26(2) (2016), p. 1017, Eq. (3.19) and the displayed inequality after it

import Mathlib

open scoped RealInnerProductSpace

namespace StochQuasiNewton.SQN

/-- Eq. (3.19) and the line after it: if `F` is `C²` with `∇²F(w) ≻ λ I` for every `w` (the
lower bound of (3.4)), then `F(v) ≥ F(w) − ‖∇F(w)‖² / (2λ)` for all `v, w`, and for a minimizer
`w*` of `F`, `2λ [F(w) − F(w*)] ≤ ‖∇F(w)‖²` for every `w`. -/
theorem suboptimality_le_gradient_sq {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 2 F) (lam : ℝ) (hlam : 0 < lam)
    (hHess : ∀ w v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      lam * ‖v‖ ^ 2 < ⟪fderiv ℝ (gradient F) w v, v⟫)
    (wstar : EuclideanSpace ℝ (Fin n)) (hwstar : IsMinOn F Set.univ wstar) :
    (∀ w v : EuclideanSpace ℝ (Fin n), F w - 1 / (2 * lam) * ‖gradient F w‖ ^ 2 ≤ F v) ∧
      ∀ w : EuclideanSpace ℝ (Fin n), 2 * lam * (F w - F wstar) ≤ ‖gradient F w‖ ^ 2 := by sorry

end StochQuasiNewton.SQN
