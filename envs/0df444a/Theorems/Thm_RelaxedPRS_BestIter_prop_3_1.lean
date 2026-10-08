-- Prove2me | Theorems.Thm_RelaxedPRS_BestIter_prop_3_1
-- name    : RelaxedPRS.BestIter.prop_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:53.052013+00:00
-- url     : https://prove2.me/theorems/9ac4dd6b-8b63-4d63-b972-05118615ab8a
-- title:
--   Proposition 3.1, p. 10 — fundamental inequality under Lipschitz assumptions: 4γλ(objective error) ≤ telescoping term + multiple of ‖z − z⁺‖²
-- statement:
--   Let $f, g : \mathcal H \to (-\infty,\infty]$ be closed, proper and convex, $\gamma > 0$, $\beta > 0$, let $z^*$ be a fixed point of $T_{\mathrm{PRS}}$ and $x^* = \mathbf{prox}_{\gamma g}(z^*)$. Let $\lambda > 0$, $z \in \mathcal H$ and $z^+ = (T_{\mathrm{PRS}})_\lambda z$. If $\nabla f$ is $(1/\beta)$-Lipschitz, set $x = x_g = \mathbf{prox}_{\gamma g}(z)$; if $\nabla g$ is $(1/\beta)$-Lipschitz, set $x = x_f = \mathbf{prox}_{\gamma f}(\mathbf{refl}_{\gamma g}(z))$. In either case
--   $$4\gamma\lambda\big(f(x) + g(x) - f(x^*) - g(x^*)\big) \le \begin{cases} \|z - z^*\|^2 - \|z^+ - z^*\|^2 + \Big(1 + \frac{1}{2\lambda}\big(\frac\gamma\beta - 1\big)\Big)\|z - z^+\|^2, & \text{if } \gamma \le \beta;\\[4pt] \Big(1 + \frac{\gamma - \beta}{2\beta}\Big)\big(\|z - z^*\|^2 - \|z^+ - z^*\|^2 + \|z - z^+\|^2\big), & \text{otherwise.}\end{cases}$$
--
--   The right-hand side is a telescoping term plus a multiple of the fixed-point residual, so along a relaxed PRS run the weighted objective errors are summable. This is the key estimate behind Theorem 3.1.
--
--   **Formalization Note** The two cases of "respectively" are two separate conjuncts, each under its own Lipschitz hypothesis; note which point the error is evaluated at in each. In the case $\gamma \le \beta$ the coefficient $1 + \frac1{2\lambda}(\frac\gamma\beta - 1)$ may be negative, as on the page. The objective error is a real number; every value involved is finite (see the Setting).
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 10, Proposition 3.1; proof on p. 32, Appendix A

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_RelaxedPRS_BestIter_Setting
open ThreeOpSplitting.ConvexRates MoreauProx.Characterization Filter

namespace RelaxedPRS.BestIter

theorem prop_3_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H) (hPf : IsProx γ f Pf) (hPg : IsProx γ g Pg)
    (zs : H) (hzs : RelaxedPRS.StrongCvx.TPRS Pf Pg zs = zs) (β : ℝ) (hβ : 0 < β)
    (t : ℝ) (ht0 : 0 < t) (w : H) :
    (RelaxedPRS.StrongCvx.HasLipGrad β f →
      4 * γ * t * objErr f g (xg Pg zs) (xg Pg w) ≤
        if γ ≤ β then
          ‖w - zs‖ ^ 2 - ‖RelaxedPRS.StrongCvx.Tlam Pf Pg t w - zs‖ ^ 2
            + (1 + 1 / (2 * t) * (γ / β - 1)) * ‖w - RelaxedPRS.StrongCvx.Tlam Pf Pg t w‖ ^ 2
        else
          (1 + (γ - β) / (2 * β)) *
            (‖w - zs‖ ^ 2 - ‖RelaxedPRS.StrongCvx.Tlam Pf Pg t w - zs‖ ^ 2 + ‖w - RelaxedPRS.StrongCvx.Tlam Pf Pg t w‖ ^ 2)) ∧
    (RelaxedPRS.StrongCvx.HasLipGrad β g →
      4 * γ * t * objErr f g (xg Pg zs) (RelaxedPRS.StrongCvx.xf Pf Pg w) ≤
        if γ ≤ β then
          ‖w - zs‖ ^ 2 - ‖RelaxedPRS.StrongCvx.Tlam Pf Pg t w - zs‖ ^ 2
            + (1 + 1 / (2 * t) * (γ / β - 1)) * ‖w - RelaxedPRS.StrongCvx.Tlam Pf Pg t w‖ ^ 2
        else
          (1 + (γ - β) / (2 * β)) *
            (‖w - zs‖ ^ 2 - ‖RelaxedPRS.StrongCvx.Tlam Pf Pg t w - zs‖ ^ 2 + ‖w - RelaxedPRS.StrongCvx.Tlam Pf Pg t w‖ ^ 2)) := by sorry

end RelaxedPRS.BestIter
