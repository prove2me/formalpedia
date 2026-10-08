-- Prove2me | Theorems.Thm_RelaxedPRS_Linear_eq_4_7
-- name    : RelaxedPRS.Linear.eq_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:13.642781+00:00
-- url     : https://prove2.me/theorems/a9c4e53c-f0c7-4244-966f-8a711de1458e
-- title:
--   (4.7) — fixed-point distance bound
-- statement:
--   In the relaxed PRS setting, suppose $g$ is real valued, convex, differentiable, and has a $(1/\beta)$-Lipschitz gradient for $\beta>0$. Let $z^*$ be a fixed point of $T_{\rm PRS}$, let $x^*=P_gz^*$, and let $x_f^k,x_g^k$ be the proximal points from iteration $k$. For every $k\ge0$,
--
--   $$\|z^k-z^*\|^2\le 3\left(\|x_f^k-x^*\|^2+\|\gamma\nabla g(x_g^k)-\gamma\nabla g(x^*)\|^2+\|x_g^k-x_f^k\|^2\right).$$
--
--   This bounds the fixed-point distance by the three quantities controlled in (4.6). The equality of the selected proximal subgradient and the smooth gradient is part of the mathematical content; it is not an added hypothesis.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 16, proof of Theorem 4.3, (4.7)

import Mathlib
import Definitions.Def_RelaxedPRS_Linear_Setting

namespace RelaxedPRS.Linear

/-- (4.7), proof of Theorem 4.3, p. 16: the fixed-point distance bound. -/
theorem eq_4_7 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg)
    (lam : ℕ → ℝ) (hlam : ∀ k, 0 < lam k ∧ lam k ≤ 1)
    (z : ℕ → H) (hz : RelaxedPRS.StrongCvx.IsPRSRun Pf Pg lam z)
    (zs : H) (hzs : RelaxedPRS.StrongCvx.TPRS Pf Pg zs = zs)
    (β : ℝ) (hβ : 0 < β)
    (h : H → ℝ) (hgh : ∀ x, g x = (h x : EReal))
    (hh : ThreeOpSplitting.ConvexRates.IsSmoothConvex β h) :
    ∀ k, ‖z k - zs‖ ^ 2 ≤ 3 *
      (‖RelaxedPRS.StrongCvx.xf Pf Pg (z k) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2 +
       ‖γ • gradient h (RelaxedPRS.StrongCvx.xg Pg (z k)) - γ • gradient h (RelaxedPRS.StrongCvx.xg Pg zs)‖ ^ 2 +
       ‖RelaxedPRS.StrongCvx.xg Pg (z k) - RelaxedPRS.StrongCvx.xf Pf Pg (z k)‖ ^ 2) := by sorry
end RelaxedPRS.Linear
