-- Prove2me | Theorems.Thm_RelaxedPRS_DRSSmooth_prop_B_4
-- name    : RelaxedPRS.DRSSmooth.prop_B_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:33.707213+00:00
-- url     : https://prove2.me/theorems/a4181963-aaf7-4cf4-9e89-2585288b3eb9
-- title:
--   Proposition B.4, pp. 34–35 — summability of (3.1)
-- statement:
--   Under the same assumptions, let $z^*$ be a PRS fixed point, $x^*=P_g(z^*)$, and let $\kappa$ be the positive root of $x^3+x^2-2x-1$. Put $\theta=1-1/\kappa^2$ if $\gamma<\kappa\beta$, and $\theta=1$ otherwise. Define
--   $$b_i=2\gamma[F(x_f^i)-F(x^*)]+\theta\gamma^2\|\nabla g(x_g^{i+1})-\nabla g(x_g^i)\|^2+\frac{(1-\theta)\gamma^2}{\beta^2}\|x_g^{i+1}-x_g^i\|^2.$$
--   Then $\sum_i b_i$ converges. It is at most $\|x_g^0-x^*\|^2$ in the first case, and at most
--   $$\|x_g^0-x^*\|^2+\frac{\gamma^3/\beta-2\gamma\beta+\gamma^2-\beta^2}{\beta^2+\gamma^2}\|z^0-z^*\|^2$$
--   in the second. This provides the total bound behind Theorem 3.2.
--
--   **Formalization Note** The printed $x_f^k$ inside the sum is read as $x_f^i$; the otherwise-case coefficient includes the paper's $+\gamma^2$.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, pp. 34–35, Proposition B.4 (B.12)

import Mathlib
import Definitions.Def_RelaxedPRS_DRSSmooth_Setting

open InnerProductSpace Filter

namespace RelaxedPRS.DRSSmooth

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition B.4, pp. 34–35, (B.12); the summation index is corrected. -/
theorem prop_B_4 (f : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (g : H → ℝ) (β : ℝ) (hβ : 0 < β)
    (hg : ThreeOpSplitting.ConvexRates.IsSmoothConvex β g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ (gE g) Pg)
    (z : ℕ → H) (hz : RelaxedPRS.StrongCvx.IsPRSRun Pf Pg (fun _ => 1 / 2) z)
    (zs : H) (hzs : RelaxedPRS.StrongCvx.TPRS Pf Pg zs = zs)
    (κ : ℝ) (hκ : 0 < κ ∧ κ ^ 3 + κ ^ 2 - 2 * κ - 1 = 0) :
    let θ : ℝ := if γ < κ * β then 1 - 1 / κ ^ 2 else 1
    Summable (seqB f g Pf Pg z zs γ β θ) ∧
    (if γ < κ * β then
      (∑' i : ℕ, seqB f g Pf Pg z zs γ β θ i) ≤
        ‖RelaxedPRS.StrongCvx.xg Pg (z 0) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2
     else
      (∑' i : ℕ, seqB f g Pf Pg z zs γ β θ i) ≤
        ‖RelaxedPRS.StrongCvx.xg Pg (z 0) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2 +
          1 / (β ^ 2 + γ ^ 2) *
            (γ ^ 3 / β - 2 * γ * β + γ ^ 2 - β ^ 2) * ‖z 0 - zs‖ ^ 2) := by sorry

end RelaxedPRS.DRSSmooth
