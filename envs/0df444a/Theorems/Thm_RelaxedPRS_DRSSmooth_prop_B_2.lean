-- Prove2me | Theorems.Thm_RelaxedPRS_DRSSmooth_prop_B_2
-- name    : RelaxedPRS.DRSSmooth.prop_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:18.114287+00:00
-- url     : https://prove2.me/theorems/4f9292b4-5081-4a43-8d8c-b0add7b075b7
-- title:
--   Proposition B.2, p. 34 — monotone dominating sequence
-- statement:
--   Under the DRS and smoothness assumptions of Proposition B.1, fix a PRS fixed point $z^*$ and put $x^*=P_g(z^*)$. For every $\theta\in[0,1]$ and integer $k\ge1$,
--   $$\begin{aligned}2\gamma[F(x_f^k)-F(x^*)]&+\left(2\gamma\beta-\frac{\gamma^3}{\beta}\right)\|\nabla g(x_g^{k+1})-\nabla g(x_g^k)\|^2+\|x_g^{k+1}-x_g^k\|^2\\&\le2\gamma[F(x_f^{k-1})-F(x^*)]+\theta\gamma^2\|\nabla g(x_g^k)-\nabla g(x_g^{k-1})\|^2+\frac{(1-\theta)\gamma^2}{\beta^2}\|x_g^k-x_g^{k-1}\|^2.\end{aligned}$$
--   The bound identifies the sequence whose monotonicity yields the nonergodic rate.
--
--   **Formalization Note** $k\ge1$ keeps the predecessor index in its intended domain.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 34, Proposition B.2 (B.7)

import Mathlib
import Definitions.Def_RelaxedPRS_DRSSmooth_Setting

open InnerProductSpace Filter

namespace RelaxedPRS.DRSSmooth

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition B.2, p. 34, (B.7). -/
theorem prop_B_2 (f : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (g : H → ℝ) (β : ℝ) (hβ : 0 < β)
    (hg : ThreeOpSplitting.ConvexRates.IsSmoothConvex β g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ (gE g) Pg)
    (z : ℕ → H) (hz : RelaxedPRS.StrongCvx.IsPRSRun Pf Pg (fun _ => 1 / 2) z)
    (zs : H) (hzs : RelaxedPRS.StrongCvx.TPRS Pf Pg zs = zs) :
    ∀ (θ : ℝ), 0 ≤ θ → θ ≤ 1 → ∀ (k : ℕ), 1 ≤ k →
      2 * γ * errF f g Pf Pg z zs k +
      (2 * γ * β - γ ^ 3 / β) *
        ‖gradient g (RelaxedPRS.StrongCvx.xg Pg (z (k + 1))) - gradient g (RelaxedPRS.StrongCvx.xg Pg (z k))‖ ^ 2 +
      ‖RelaxedPRS.StrongCvx.xg Pg (z (k + 1)) - RelaxedPRS.StrongCvx.xg Pg (z k)‖ ^ 2 ≤
      2 * γ * errF f g Pf Pg z zs (k - 1) +
      θ * γ ^ 2 *
        ‖gradient g (RelaxedPRS.StrongCvx.xg Pg (z k)) - gradient g (RelaxedPRS.StrongCvx.xg Pg (z (k - 1)))‖ ^ 2 +
      (1 - θ) * γ ^ 2 / β ^ 2 *
        ‖RelaxedPRS.StrongCvx.xg Pg (z k) - RelaxedPRS.StrongCvx.xg Pg (z (k - 1))‖ ^ 2 := by sorry

end RelaxedPRS.DRSSmooth
