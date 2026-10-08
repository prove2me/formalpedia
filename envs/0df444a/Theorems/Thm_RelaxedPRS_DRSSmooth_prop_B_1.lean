-- Prove2me | Theorems.Thm_RelaxedPRS_DRSSmooth_prop_B_1
-- name    : RelaxedPRS.DRSSmooth.prop_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:27.529901+00:00
-- url     : https://prove2.me/theorems/c4ff9fdf-eb5e-451e-920c-fe99a07ef4b8
-- title:
--   Proposition B.1, p. 33 — fundamental DRS inequality
-- statement:
--   Let $f:H\to(-\infty,+\infty]$ be proper, closed and convex, and let $g:H\to\mathbb R$ be convex and differentiable with $(1/\beta)$-Lipschitz gradient, $\beta>0$. For $\gamma>0$, run DRS with the proximal maps of $f$ and $g$. For every $k\ge0$ and $x\in\operatorname{dom}f$,
--   $$\begin{aligned}2\gamma[F(x_f^k)-F(x)]&+\left(2\gamma\beta-\frac{\gamma^3}{\beta}\right)\|\nabla g(x_g^{k+1})-\nabla g(x_g^k)\|^2\\&+\|x_g^{k+1}-x\|^2+\|x_g^{k+1}-x_g^k\|^2\le\|x_g^k-x\|^2,\end{aligned}$$
--   where $F=f+g$. This is the stepwise estimate used for the objective rates.
--
--   **Formalization Note** DRS is the relaxed PRS run with constant relaxation $1/2$; the finite $f$ values are represented by real conversions.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 33, Proposition B.1 (B.4)

import Mathlib
import Definitions.Def_RelaxedPRS_DRSSmooth_Setting

open InnerProductSpace Filter

namespace RelaxedPRS.DRSSmooth

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition B.1, p. 33, (B.4). -/
theorem prop_B_1 (f : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (g : H → ℝ) (β : ℝ) (hβ : 0 < β)
    (hg : ThreeOpSplitting.ConvexRates.IsSmoothConvex β g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ (gE g) Pg)
    (z : ℕ → H) (hz : RelaxedPRS.StrongCvx.IsPRSRun Pf Pg (fun _ => 1 / 2) z) :
    ∀ (k : ℕ) (x : H), f x ≠ ⊤ →
      2 * γ * ((f (RelaxedPRS.StrongCvx.xf Pf Pg (z k))).toReal + g (RelaxedPRS.StrongCvx.xf Pf Pg (z k)) - (f x).toReal - g x) +
      (2 * γ * β - γ ^ 3 / β) *
        ‖gradient g (RelaxedPRS.StrongCvx.xg Pg (z (k + 1))) - gradient g (RelaxedPRS.StrongCvx.xg Pg (z k))‖ ^ 2 +
      ‖RelaxedPRS.StrongCvx.xg Pg (z (k + 1)) - x‖ ^ 2 +
      ‖RelaxedPRS.StrongCvx.xg Pg (z (k + 1)) - RelaxedPRS.StrongCvx.xg Pg (z k)‖ ^ 2 ≤
      ‖RelaxedPRS.StrongCvx.xg Pg (z k) - x‖ ^ 2 := by sorry

end RelaxedPRS.DRSSmooth
