-- Prove2me | Theorems.Thm_TrustIPM_lemma_5
-- name    : TrustIPM.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:18:04.452819+00:00
-- url     : https://prove2.me/theorems/1514cbdb-eb0c-4081-b1cb-3f02fc06a52c
-- title:
--   Lemma 5 — the model $\mathcal M^{\psi_\mu}_x$ predicts the barrier change up to a cubic error
-- statement:
--   Suppose Assumption 1 holds and $\mu>0$. Let $x\in\mathcal X$, $S=\mathrm{diag}(a(x))$, $d_x\in\mathbb R^n$, $d_s=\nabla a(x)d_x$, $y=\mu S^{-1}\mathbf 1$ and $\kappa\in(0,1/4]$. If
--
--   $$
--   \|S^{-1}d_s\|_2+\frac{L_1\|d_x\|_2^2\|y\|_2}{\mu}\le\kappa ,\tag{8}
--   $$
--
--   then
--
--   1. the segment $\mathrm{Convex}\{x,x+d_x\}$ lies in $\mathcal X$, and
--   2. $$\bigl|\psi_\mu(x)+\mathcal M^{\psi_\mu}_x(d_x)-\psi_\mu(x+d_x)\bigr|\le\frac{L_2}6(1+2\|y\|_1)\|d_x\|_2^3+\frac43L_1\|d_x\|_2^2\|y\|_1\kappa+\frac53\mu\kappa^3 .$$
--
--   The lemma turns the predicted reduction $\mathcal M^{\psi_\mu}_x(d_x)$ into an actual reduction of the log barrier.
--
--   Differences from the source: none.
-- source:
--   Hinder & Ye, Worst-case iteration bounds for log barrier methods on problems with nonconvex constraints, arXiv:1807.00404v5, Lemma 5, p.9; standing µ > 0 from (3), p.2

import Mathlib
import Definitions.Def_TrustIPM_barrier

namespace TrustIPM

/-- **Lemma 5** (Hinder & Ye, *Worst-case iteration bounds for log barrier methods on problems with
nonconvex constraints*, arXiv:1807.00404v5, Lemma 5, p.9). Suppose Assumption 1 holds. Let `x ∈ X`,
`S = diag(a(x))`, `d_x ∈ ℝⁿ`, `d_s = ∇a(x)d_x`, `y = µS⁻¹1`, and `κ ∈ (0, 1/4]`. If
`‖S⁻¹d_s‖₂ + L₁‖d_x‖₂²‖y‖₂/µ ≤ κ` (8), then `Convex{x, x + d_x} ⊆ X` and
`|ψµ(x) + M^{ψµ}_x(d_x) − ψµ(x + d_x)| ≤ (L₂/6)(1 + 2‖y‖₁)‖d_x‖₂³ + (4/3)L₁‖d_x‖₂²‖y‖₁κ + (5/3)µκ³`.

**Formalization Note** `Convex{x, x + d_x}` is `segment ℝ x (x + d)`. `µ > 0` is the barrier
parameter of (3), p.2; `n, m` are positive integers (p.1). -/
theorem lemma_5 {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (f : E n → ℝ) (a : Fin m → E n → ℝ)
    (L₁ L₂ μ κ : ℝ) (x d : E n) (hA1 : Assumption1 f a L₁ L₂) (hμ : 0 < μ)
    (hx : x ∈ feasibleSet a) (hκ : 0 < κ) (hκ' : κ ≤ 1 / 4)
    (h8 : norm2 (scaledSlackDir a x d) + L₁ * ‖d‖ ^ 2 * norm2 (centralDual a μ x) / μ ≤ κ) :
    segment ℝ x (x + d) ⊆ feasibleSet a ∧
      |barrier f a μ x + model f a μ x d - barrier f a μ (x + d)| ≤
        L₂ / 6 * (1 + 2 * norm1 (centralDual a μ x)) * ‖d‖ ^ 3 +
          4 / 3 * L₁ * ‖d‖ ^ 2 * norm1 (centralDual a μ x) * κ + 5 / 3 * μ * κ ^ 3 := by sorry

end TrustIPM
