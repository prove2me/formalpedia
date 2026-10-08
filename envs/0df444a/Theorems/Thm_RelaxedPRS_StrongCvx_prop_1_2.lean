-- Prove2me | Theorems.Thm_RelaxedPRS_StrongCvx_prop_1_2
-- name    : RelaxedPRS.StrongCvx.prop_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:52.631715+00:00
-- url     : https://prove2.me/theorems/1a5cf730-abd3-470a-abcd-8bd3828c20d9
-- title:
--   Proposition 1.2 — upper fundamental inequality (1.15)
-- statement:
--   Let $f,g$ be closed, proper, convex functions with regularity terms $S_f,S_g$, and let $z^+=T_\lambda z$ for $\lambda>0$ and $\gamma>0$. At $x$ where both functions admit subgradients, with proximal auxiliary points $x_f,x_g$, the upper fundamental inequality is
--   $$4\gamma\lambda\bigl(f(x_f)+g(x_g)-f(x)-g(x)+S_f(x_f,x)+S_g(x_g,x)\bigr)\le\|z-x\|^2-\|z^+-x\|^2+\left(1-\frac1\lambda\right)\|z^+-z\|^2.$$
--   The subgradients at $x$ may be any members of the respective subdifferentials. This estimate is the upper half of the one-step analysis.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 8, Proposition 1.2, (1.15)

import Mathlib
import Definitions.Def_RelaxedPRS_StrongCvx_Setting

open scoped InnerProductSpace

namespace RelaxedPRS.StrongCvx

/-- Proposition 1.2, p. 8: the upper fundamental inequality (1.15). -/
theorem prop_1_2 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg)
    (μf βf μg βg : ℝ)
    (hμf : 0 ≤ μf) (hβf : 0 ≤ βf) (hμg : 0 ≤ μg) (hβg : 0 ≤ βg)
    (hscf : IsStrongCvxE μf f) (hscg : IsStrongCvxE μg g)
    (hlf : 0 < βf → HasLipGrad βf f)
    (hlg : 0 < βg → HasLipGrad βg g)
    (lam : ℝ) (hlam : 0 < lam) (z x u v : H)
    (hu : u ∈ MoreauProx.Characterization.subgrad f x)
    (hv : v ∈ MoreauProx.Characterization.subgrad g x) :
    let zp := Tlam Pf Pg lam z
    4 * γ * lam *
      ((f (xf Pf Pg z)).toReal + (g (xg Pg z)).toReal -
       (f x).toReal - (g x).toReal +
       auxS μf βf (xf Pf Pg z) x (gtF γ Pf Pg z) u +
       auxS μg βg (xg Pg z) x (gtG γ Pg z) v) ≤
      ‖z - x‖ ^ 2 - ‖zp - x‖ ^ 2 +
        (1 - 1 / lam) * ‖zp - z‖ ^ 2 := by sorry

end RelaxedPRS.StrongCvx
