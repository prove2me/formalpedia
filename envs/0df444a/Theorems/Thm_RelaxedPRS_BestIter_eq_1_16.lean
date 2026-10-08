-- Prove2me | Theorems.Thm_RelaxedPRS_BestIter_eq_1_16
-- name    : RelaxedPRS.BestIter.eq_1_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:50.357222+00:00
-- url     : https://prove2.me/theorems/150462c0-f0ca-440d-976b-45a0fed9c923
-- title:
--   (1.16), Proposition 1.2, p. 8 — upper fundamental inequality at x*, with one (1/β)-Lipschitz gradient
-- statement:
--   Let $f, g : \mathcal H \to (-\infty,\infty]$ be closed, proper and convex, $\gamma > 0$, $\beta > 0$, let $z^*$ be a fixed point of $T_{\mathrm{PRS}}$ and $x^* = \mathbf{prox}_{\gamma g}(z^*)$. Let $\lambda > 0$, $z \in \mathcal H$, $z^+ = (T_{\mathrm{PRS}})_\lambda z$, and let $x_g$, $x_f$ be the points of Lemma 1.1 for $z$.
--
--   1. If $f$ is real-valued and differentiable with $(1/\beta)$-Lipschitz gradient, then
--   $$4\gamma\lambda\Big(f(x_f) + g(x_g) - f(x^*) - g(x^*) + \tfrac{\beta}{2}\|\nabla f(x_f) - \nabla f(x^*)\|^2\Big) \le \|z - z^*\|^2 - \|z^+ - z^*\|^2 + 2\langle z - z^+, z^* - x^*\rangle + \Big(1 - \frac1\lambda\Big)\|z^+ - z\|^2.$$
--   2. If $g$ is real-valued and differentiable with $(1/\beta)$-Lipschitz gradient, the same holds with the regularity term $\frac{\beta}{2}\|\nabla g(x_g) - \nabla g(x^*)\|^2$ in place of $\frac{\beta}{2}\|\nabla f(x_f) - \nabla f(x^*)\|^2$.
--
--   This is the paper's inequality (1.16) in the setting of Section 3, where neither function is assumed strongly convex and only one has a Lipschitz gradient: there $S_f(x_f, x^*) = \frac\beta2\|\nabla f(x_f) - \nabla f(x^*)\|^2$ for the smooth function and the other $S$-term vanishes. It is the starting point of the proof of Proposition 3.1.
--
--   **Formalization Note** This is the instance $\mu_f = \mu_g = 0$, $\beta_f = \beta$, $\beta_g = 0$ (case 1) or $\beta_f = 0$, $\beta_g = \beta$ (case 2) of (1.16), which the paper's §1.10 convention ("we also allow the strong convexity or Lipschitz differentiability constants to vanish") permits. For a differentiable convex function the prox subgradient $\widetilde\nabla f$ is the gradient. All function values appearing are finite (prox outputs, or values of the real-valued smooth function) and are written as real numbers. As on the page (p. 4: "Let $\lambda > 0$"), the relaxation is any $\lambda > 0$.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 8, Proposition 1.2, (1.16); p. 7–8, (1.13)–(1.14)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_RelaxedPRS_BestIter_Setting
open ThreeOpSplitting.ConvexRates MoreauProx.Characterization Filter

namespace RelaxedPRS.BestIter

theorem eq_1_16 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H) (hPf : IsProx γ f Pf) (hPg : IsProx γ g Pg)
    (zs : H) (hzs : RelaxedPRS.StrongCvx.TPRS Pf Pg zs = zs) (β : ℝ) (hβ : 0 < β)
    (t : ℝ) (ht0 : 0 < t) (w : H) :
    (∀ h : H → ℝ, (∀ x, f x = (h x : EReal)) → IsSmoothConvex β h →
      4 * γ * t * (h (RelaxedPRS.StrongCvx.xf Pf Pg w) + (g (xg Pg w)).toReal - h (xg Pg zs) - (g (xg Pg zs)).toReal
          + β / 2 * ‖gradient h (RelaxedPRS.StrongCvx.xf Pf Pg w) - gradient h (xg Pg zs)‖ ^ 2)
        ≤ ‖w - zs‖ ^ 2 - ‖RelaxedPRS.StrongCvx.Tlam Pf Pg t w - zs‖ ^ 2
          + 2 * inner ℝ (w - RelaxedPRS.StrongCvx.Tlam Pf Pg t w) (zs - xg Pg zs)
          + (1 - 1 / t) * ‖RelaxedPRS.StrongCvx.Tlam Pf Pg t w - w‖ ^ 2) ∧
    (∀ h : H → ℝ, (∀ x, g x = (h x : EReal)) → IsSmoothConvex β h →
      4 * γ * t * ((f (RelaxedPRS.StrongCvx.xf Pf Pg w)).toReal + h (xg Pg w) - (f (xg Pg zs)).toReal - h (xg Pg zs)
          + β / 2 * ‖gradient h (xg Pg w) - gradient h (xg Pg zs)‖ ^ 2)
        ≤ ‖w - zs‖ ^ 2 - ‖RelaxedPRS.StrongCvx.Tlam Pf Pg t w - zs‖ ^ 2
          + 2 * inner ℝ (w - RelaxedPRS.StrongCvx.Tlam Pf Pg t w) (zs - xg Pg zs)
          + (1 - 1 / t) * ‖RelaxedPRS.StrongCvx.Tlam Pf Pg t w - w‖ ^ 2) := by sorry

end RelaxedPRS.BestIter
