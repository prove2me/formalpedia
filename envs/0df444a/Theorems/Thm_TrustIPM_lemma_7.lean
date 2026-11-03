-- Prove2me | Theorems.Thm_TrustIPM_lemma_7
-- name    : TrustIPM.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:18:07.145011+00:00
-- url     : https://prove2.me/theorems/952e13c6-631d-4541-a0f1-cbbd1cf01a12
-- title:
--   Lemma 7 — error of the linearized gradient of the Lagrangian
-- statement:
--   Suppose Assumption 1 holds. Let $y,y^+\in\mathbb R^m$ with all $y_i\neq0$, $Y=\mathrm{diag}(y)$, and $\mathrm{Convex}\{x,x^+\}\subseteq\mathcal X$. With $d_x=x^+-x$ and $d_y=y^+-y$,
--
--   $$
--   \bigl\|\nabla_x\mathcal L(x,y)+\nabla^2_{xx}\mathcal L(x,y)^Td_x-d_y^T\nabla_xa(x)-\nabla_x\mathcal L(x^+,y^+)\bigr\|_2\le L_1\|y\|_2\|d_x\|_2\|Y^{-1}d_y\|_2+\frac{L_2}2(\|y\|_1+1)\|d_x\|_2^2 .\tag{15}
--   $$
--
--   Here $d_y^T\nabla_xa(x)=\sum_id_{y,i}\nabla a_i(x)$. The lemma is the source of (SIP1.c) at the new iterate.
--
--   **Formalization Note** $\nabla^2_{xx}\mathcal L(x,y)^Td_x$ is written as $\nabla^2_{xx}\mathcal L(x,y)d_x$; the Hessian of a twice differentiable function is symmetric.
--
--   Differences from the source:
--   - encoding: Y⁻¹d_y in (15) → hypothesis yᵢ ≠ 0 for every i; reason: it only excludes the cases where Y⁻¹d_y is undefined
--   - encoding: ∇²ₓₓL(x, y)ᵀd_x → hessLag f a x y d_x (no transpose); reason: the Hessian of a twice differentiable function is symmetric; same value
-- source:
--   Hinder & Ye, Worst-case iteration bounds for log barrier methods on problems with nonconvex constraints, arXiv:1807.00404v5, Lemma 7, p.12

import Mathlib
import Definitions.Def_TrustIPM_barrier

namespace TrustIPM

/-- **Lemma 7** (Hinder & Ye, *Worst-case iteration bounds for log barrier methods on problems with
nonconvex constraints*, arXiv:1807.00404v5, Lemma 7, p.12). Suppose Assumption 1 holds. Let
`y, y⁺ ∈ ℝᵐ` and `Convex{x, x⁺} ⊆ X`. Then, with `d_x = x⁺ − x` and `d_y = y⁺ − y`,
`‖∇ₓL(x, y) + ∇²ₓₓL(x, y)ᵀd_x − d_yᵀ∇ₓa(x) − ∇ₓL(x⁺, y⁺)‖₂
  ≤ L₁‖y‖₂‖d_x‖₂‖Y⁻¹d_y‖₂ + (L₂/2)(‖y‖₁ + 1)‖d_x‖₂²` (15).

**Formalization Note** `d_yᵀ∇ₓa(x)` is the vector `Σᵢ (d_y)ᵢ ∇aᵢ(x)` (`jacT`). The Hessian of the
Lagrangian is self-adjoint where it is the classical one, so `∇²ₓₓL(x, y)ᵀd_x` is
`hessLag f a x y d_x`. `Y = diag(y)` must be invertible, so `yᵢ ≠ 0` for every `i`; `n, m` are
positive integers (p.1). -/
theorem lemma_7 {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (f : E n → ℝ) (a : Fin m → E n → ℝ)
    (L₁ L₂ : ℝ) (x xp : E n) (y yp : Fin m → ℝ) (hA1 : Assumption1 f a L₁ L₂)
    (hseg : segment ℝ x xp ⊆ feasibleSet a) (hy : ∀ i, y i ≠ 0) :
    ‖gradLag f a x y + hessLag f a x y (xp - x) - jacT a x (yp - y) - gradLag f a xp yp‖ ≤
      L₁ * norm2 y * ‖xp - x‖ * norm2 (fun i => (yp i - y i) / y i) +
        L₂ / 2 * (norm1 y + 1) * ‖xp - x‖ ^ 2 := by sorry

end TrustIPM
