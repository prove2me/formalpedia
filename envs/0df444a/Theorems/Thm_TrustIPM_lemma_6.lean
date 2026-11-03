-- Prove2me | Theorems.Thm_TrustIPM_lemma_6
-- name    : TrustIPM.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:59.377972+00:00
-- url     : https://prove2.me/theorems/06031c80-27e0-4635-86e3-118ae06f9560
-- title:
--   Lemma 6 — perturbed complementarity after a primal-dual step
-- statement:
--   Suppose Assumption 1 holds and $\mu>0$. Let $\mathrm{Convex}\{x,x^+\}\subseteq\mathcal X$, $s=a(x)$, $s^+=a(x^+)$, $S=\mathrm{diag}(s)$, $y\in\mathbb R^m$ with all $y_i\neq0$, $Y=\mathrm{diag}(y)$, $y^+\in\mathbb R^m$, $Y^+=\mathrm{diag}(y^+)$, $d_x=x^+-x$, $d_y=y^+-y$ and $d_s=\nabla a(x)d_x$. If $Sy+Sd_y+Yd_s=\mu\mathbf 1$, then
--
--   1. $$\|Y^{-1}d_y\|_2\le\|S^{-1}d_s\|_2+\|\mu(SY)^{-1}\mathbf 1-\mathbf 1\|_2 ,\tag{12}$$
--   2. $$\|Y^+s^+-\mu\mathbf 1\|_2\le\|Sy\|_\infty\|S^{-1}d_s\|_2\|Y^{-1}d_y\|_2+\frac{L_1}2\|y\|_2\bigl(1+\|Y^{-1}d_y\|_2\bigr)\|d_x\|_2^2 ,\tag{13}$$
--   3. if moreover $\|Y^+s^+-\mu\mathbf 1\|_\infty<\mu$ and $\|Y^{-1}d_y\|_\infty\le1$, then $s^+>0$ and $y^+>0$.
--
--   This is the source of (SIP1.a) and (SIP1.b) at the new iterate.
--
--   Differences from the source:
--   - encoding: Y = diag(y) with Y⁻¹ used in (12), (13) → hypothesis yᵢ ≠ 0 for every i; reason: it only excludes the cases where Y⁻¹d_y is undefined
-- source:
--   Hinder & Ye, Worst-case iteration bounds for log barrier methods on problems with nonconvex constraints, arXiv:1807.00404v5, Lemma 6, p.11; standing µ > 0 from (3), p.2

import Mathlib
import Definitions.Def_TrustIPM_barrier

namespace TrustIPM

/-- **Lemma 6** (Hinder & Ye, *Worst-case iteration bounds for log barrier methods on problems with
nonconvex constraints*, arXiv:1807.00404v5, Lemma 6, p.11). Suppose Assumption 1 holds. Let
`Convex{x, x⁺} ⊆ X`, `s = a(x)`, `s⁺ = a(x⁺)`, `S = diag(a(x))`, `Y = diag(y)`, `y⁺ ∈ ℝᵐ`,
`Y⁺ = diag(y⁺)`, `d_x = x⁺ − x`, `d_y = y⁺ − y`, `d_s = ∇a(x)d_x`. If `Sy + Sd_y + Yd_s = µ1`, then
`‖Y⁻¹d_y‖₂ ≤ ‖S⁻¹d_s‖₂ + ‖µ(SY)⁻¹1 − 1‖₂` (12) and
`‖Y⁺s⁺ − µ1‖₂ ≤ ‖Sy‖∞‖S⁻¹d_s‖₂‖Y⁻¹d_y‖₂ + (L₁/2)‖y‖₂(1 + ‖Y⁻¹d_y‖₂)‖d_x‖₂²` (13).
Furthermore, if `‖Y⁺s⁺ − µ1‖∞ < µ` and `‖Y⁻¹d_y‖∞ ≤ 1` then `s⁺, y⁺ ∈ ℝᵐ₊₊`.

**Formalization Note** `Y⁻¹` must exist, so `yᵢ ≠ 0` for every `i`; `y` is otherwise arbitrary, as on
the page. `µ > 0` is the barrier parameter of (3), p.2; `n, m` are positive integers (p.1). -/
theorem lemma_6 {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (f : E n → ℝ) (a : Fin m → E n → ℝ)
    (L₁ L₂ μ : ℝ) (x xp : E n) (y yp : Fin m → ℝ) (hA1 : Assumption1 f a L₁ L₂) (hμ : 0 < μ)
    (hseg : segment ℝ x xp ⊆ feasibleSet a) (hy : ∀ i, y i ≠ 0)
    (hcent : ∀ i, a i x * y i + a i x * (yp i - y i) + y i * jac a x (xp - x) i = μ) :
    norm2 (fun i => (yp i - y i) / y i) ≤
        norm2 (scaledSlackDir a x (xp - x)) + norm2 (fun i => μ / (a i x * y i) - 1) ∧
      norm2 (fun i => yp i * a i xp - μ) ≤
        normInf (fun i => a i x * y i) * norm2 (scaledSlackDir a x (xp - x)) *
            norm2 (fun i => (yp i - y i) / y i) +
          L₁ / 2 * norm2 y * (1 + norm2 (fun i => (yp i - y i) / y i)) * ‖xp - x‖ ^ 2 ∧
      (normInf (fun i => yp i * a i xp - μ) < μ → normInf (fun i => (yp i - y i) / y i) ≤ 1 →
        (∀ i, 0 < a i xp) ∧ ∀ i, 0 < yp i) := by sorry

end TrustIPM
