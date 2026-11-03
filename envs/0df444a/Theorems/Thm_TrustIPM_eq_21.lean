-- Prove2me | Theorems.Thm_TrustIPM_eq_21
-- name    : TrustIPM.eq_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:18:09.53682+00:00
-- url     : https://prove2.me/theorems/6f499848-e6fa-4c76-ad4a-dc2aafbf9cb0
-- title:
--   Display (21) — $\|S^{-1}d_s\|_2$ bounded by the predicted progress of the trust-region step
-- statement:
--   Let $f$ and $a$ be thrice differentiable, $\mu,L_1>0$, $x\in\mathcal X$, $S=\mathrm{diag}(a(x))$, $y=\mu S^{-1}\mathbf 1$, $r\ge0$, $d_x\in\operatorname{argmin}_{u\in B_r(0)}\mathcal M^{\psi_\mu}_x(u)$ and $d_s=\nabla a(x)d_x$. If $\|\nabla^2f(x)\|_2\le L_1$ and $\|\nabla^2a_i(x)\|_2\le L_1$ for every $i$, then
--
--   $$
--   \|S^{-1}d_s\|_2\le\sqrt{\frac{L_1(1+\|y\|_1)\|d_x\|_2^2-2\mathcal M^{\psi_\mu}_x(d_x)}{\mu}} .\tag{21}
--   $$
--
--   A large slack step forces a large predicted decrease of the barrier; this is what makes the adaptive step size of Algorithm 1 work.
--
--   Differences from the source:
--   - generalization: d_x ∈ argmin over B_r(0) with r from line 16 of Algorithm 1 ('as per Algorithm 1') → every radius r ≥ 0; reason: the derivation (Lemma 9) holds for every r ≥ 0; taking r from line 16 gives the source's statement
-- source:
--   Hinder & Ye, Worst-case iteration bounds for log barrier methods on problems with nonconvex constraints, arXiv:1807.00404v5, display (21), p.14 (with the setting of the paragraph above it)

import Mathlib
import Definitions.Def_TrustIPM_barrier

namespace TrustIPM

/-- **Display (21)** (Hinder & Ye, *Worst-case iteration bounds for log barrier methods on problems
with nonconvex constraints*, arXiv:1807.00404v5, display (21), p.14). Let `x ∈ X`, `S = diag(a(x))`,
`y = µS⁻¹1`, `d_s = ∇a(x)d_x` and `d_x ∈ argmin_{u ∈ B_r(0)} M^{ψµ}_x(u)`. If `‖∇²f(x)‖₂ ≤ L₁` and
`‖∇²aᵢ(x)‖₂ ≤ L₁` for every `i`, then
`‖S⁻¹d_s‖₂ ≤ ((L₁(1 + ‖y‖₁)‖d_x‖₂² − 2M^{ψµ}_x(d_x))/µ)^{1/2}`.

**Formalization Note** The page takes `r` from line 16 of Algorithm 1 ("as per Algorithm 1"); the
statement holds for every radius `r ≥ 0` and is stated so. `‖∇²f(x)‖₂` is the operator (spectral)
norm of `hess f x`. `f` and `a` are thrice differentiable on `ℝⁿ` (the standing assumption of p.1),
`µ, L₁ > 0`, and `n, m` are positive integers. -/
theorem eq_21 {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (f : E n → ℝ) (a : Fin m → E n → ℝ)
    (L₁ μ r : ℝ) (x d : E n) (hf : ThriceDifferentiable f)
    (ha : ∀ i, ThriceDifferentiable (a i)) (hμ : 0 < μ) (hL₁ : 0 < L₁)
    (hx : x ∈ feasibleSet a) (hr : 0 ≤ r) (hd : d ∈ Metric.closedBall 0 r)
    (hmin : IsMinOn (model f a μ x) (Metric.closedBall 0 r) d)
    (hHf : ‖hess f x‖ ≤ L₁) (hHa : ∀ i, ‖hess (a i) x‖ ≤ L₁) :
    norm2 (scaledSlackDir a x d) ≤
      Real.sqrt ((L₁ * (1 + norm1 (centralDual a μ x)) * ‖d‖ ^ 2 - 2 * model f a μ x d) / μ) := by sorry

end TrustIPM
