-- Prove2me | Theorems.Thm_RelaxedPRS_DRSSmooth_theorem_3_2
-- name    : RelaxedPRS.DRSSmooth.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:23.074918+00:00
-- url     : https://prove2.me/theorems/07e81721-e3fa-42c8-9771-445c11f39114
-- title:
--   Theorem 3.2, p. 12 — DRS objective rates
-- statement:
--   Let $f:H\to(-\infty,+\infty]$ be proper, closed and convex, and let $g:H\to\mathbb R$ be convex and differentiable with $(1/\beta)$-Lipschitz gradient, $\beta>0$. Run DRS with stepsize $\gamma>0$, start $z^0$, and fixed point $z^*$; write $x^*=P_g(z^*)$ and $e_i=f(x_f^i)+g(x_f^i)-f(x^*)-g(x^*)$. Let $\rho>0$ and $\kappa>0$ be the positive roots of $\rho^3-2\rho-1=0$ (so $\rho=(1+\sqrt5)/2\approx1.618$) and $\kappa^3+\kappa^2-2\kappa-1=0$ ($\kappa\approx1.24698$), respectively. Then
--   $$\min_{0\le i\le k} e_i\le\frac1{2\gamma(k+1)}\begin{cases}\|x_g^0-x^*\|^2,&\gamma<\rho\beta,\\\|x_g^0-x^*\|^2+\frac{\gamma^3/\beta-2\gamma\beta-\beta^2}{\beta^2+\gamma^2}\|z^0-z^*\|^2,&\gamma\ge\rho\beta.\end{cases}$$
--   For every $\gamma>0$, the best-iterate error is $o(1/(k+1))$. If $\gamma<\kappa\beta$, then every $e_k\le\|x_g^0-x^*\|^2/[2\gamma(k+1)]$ and $e_k=o(1/(k+1))$.
--
--   This is the objective convergence rate for DRS with one smooth summand.
--
--   **Formalization Note** DRS uses relaxation $\lambda_k=1/2$ (the section's standing Assumption 5). The minimum is a nonempty finite minimum, and $o$ is a genuine little-o limit. The threshold $\rho$ is corrected. The page defines $\rho\approx2.2056$ as the positive root of $x^3-2x^2-1$. The proof's display (3.2) needs $\gamma^3/\beta-2\gamma\beta-\beta^2\le0$, which in $t=\gamma/\beta$ reads $t^3-2t-1\le0$, so the threshold is the positive root of $x^3-2x-1$. With the printed $\rho$ the first case is false: for $H=\mathbb R$, $f=0$, $g(x)=x^2/(2\beta)$, $\gamma=2\beta$ and $k=0$, the error is twice the bound. The second case holds for every $\gamma\ge\rho\beta$ with the corrected $\rho$.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 12, Theorem 3.2

import Mathlib
import Definitions.Def_RelaxedPRS_DRSSmooth_Setting

open InnerProductSpace Filter

namespace RelaxedPRS.DRSSmooth

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.2, p. 12: best-iterate and nonergodic DRS objective rates.

Corrected threshold: the page defines ρ as the positive root of x³ − 2x² − 1 (ρ ≈ 2.2056), but the
proof (display (3.2)) needs γ³/β − 2γβ − β² ≤ 0, i.e. t³ − 2t − 1 ≤ 0 with t = γ/β, whose positive
root is the golden ratio (≈ 1.618). With the printed ρ the first case is false: f = 0,
g(x) = x²/(2β) on ℝ, γ = 2β, k = 0 gives an error twice the bound. Here ρ is the positive root of
x³ − 2x − 1. -/
theorem theorem_3_2 (f : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (g : H → ℝ) (β : ℝ) (hβ : 0 < β)
    (hg : ThreeOpSplitting.ConvexRates.IsSmoothConvex β g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ (gE g) Pg)
    (z : ℕ → H) (hz : RelaxedPRS.StrongCvx.IsPRSRun Pf Pg (fun _ => 1 / 2) z)
    (zs : H) (hzs : RelaxedPRS.StrongCvx.TPRS Pf Pg zs = zs)
    (ρ : ℝ) (hρ : 0 < ρ ∧ ρ ^ 3 - 2 * ρ - 1 = 0)
    (κ : ℝ) (hκ : 0 < κ ∧ κ ^ 3 + κ ^ 2 - 2 * κ - 1 = 0) :
    (γ < ρ * β → ∀ k : ℕ,
      (Finset.range (k + 1)).inf' (Finset.nonempty_range_add_one) (errF f g Pf Pg z zs) ≤
        ‖RelaxedPRS.StrongCvx.xg Pg (z 0) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2 / (2 * γ * ((k : ℝ) + 1))) ∧
    (ρ * β ≤ γ → ∀ k : ℕ,
      (Finset.range (k + 1)).inf' (Finset.nonempty_range_add_one) (errF f g Pf Pg z zs) ≤
        (‖RelaxedPRS.StrongCvx.xg Pg (z 0) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2 +
          1 / (β ^ 2 + γ ^ 2) *
            (γ ^ 3 / β - 2 * γ * β - β ^ 2) * ‖z 0 - zs‖ ^ 2) /
            (2 * γ * ((k : ℝ) + 1))) ∧
    (fun k : ℕ => (Finset.range (k + 1)).inf' (Finset.nonempty_range_add_one)
      (errF f g Pf Pg z zs)) =o[atTop] (fun k : ℕ => 1 / ((k : ℝ) + 1)) ∧
    (γ < κ * β →
      (∀ k : ℕ, errF f g Pf Pg z zs k ≤
        ‖RelaxedPRS.StrongCvx.xg Pg (z 0) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2 / (2 * γ * ((k : ℝ) + 1))) ∧
      (errF f g Pf Pg z zs) =o[atTop]
        (fun k : ℕ => 1 / ((k : ℝ) + 1))) := by sorry

end RelaxedPRS.DRSSmooth
