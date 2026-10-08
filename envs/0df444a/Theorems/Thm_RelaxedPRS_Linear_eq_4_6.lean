-- Prove2me | Theorems.Thm_RelaxedPRS_Linear_eq_4_6
-- name    : RelaxedPRS.Linear.eq_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:13.116321+00:00
-- url     : https://prove2.me/theorems/e22686e8-c522-4dcf-92e0-85b2b06845a5
-- title:
--   (4.6) — mixed-regularity decrease inequality
-- statement:
--   Assume the relaxed PRS setting with $0<\lambda_k\le1$ and fixed point $z^*$. Suppose $f$ is $\mu$-strongly convex with $\mu>0$, and $g$ is real valued with a $(1/\beta)$-Lipschitz gradient for $\beta>0$. Put $x^*=P_gz^*$ and use the proximal points $x_f^k,x_g^k$. Then, for every $k\ge0$,
--
--   $$4\gamma\lambda_k\mu\|x_f^k-x^*\|^2+4\gamma\lambda_k\beta\|\nabla g(x_g^k)-\nabla g(x^*)\|^2+4\lambda_k(1-\lambda_k)\|x_f^k-x_g^k\|^2\le\|z^k-z^*\|^2-\|z^{k+1}-z^*\|^2.$$
--
--   This is display (4.6), the mixed-regularity decrease bound for the case in which $f$ supplies strong convexity and $g$ supplies smoothness.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 16, proof of Theorem 4.3, (4.6)

import Mathlib
import Definitions.Def_RelaxedPRS_Linear_Setting

namespace RelaxedPRS.Linear

/-- (4.6), proof of Theorem 4.3, p. 16: mixed-regularity decrease. -/
theorem eq_4_6 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg)
    (lam : ℕ → ℝ) (hlam : ∀ k, 0 < lam k ∧ lam k ≤ 1)
    (z : ℕ → H) (hz : RelaxedPRS.StrongCvx.IsPRSRun Pf Pg lam z)
    (zs : H) (hzs : RelaxedPRS.StrongCvx.TPRS Pf Pg zs = zs)
    (μ β : ℝ) (hμ : 0 < μ) (hβ : 0 < β)
    (hsc : RelaxedPRS.StrongCvx.IsStrongCvxE μ f)
    (h : H → ℝ) (hgh : ∀ x, g x = (h x : EReal))
    (hh : ThreeOpSplitting.ConvexRates.IsSmoothConvex β h) :
    ∀ k, 4 * γ * lam k * μ * ‖RelaxedPRS.StrongCvx.xf Pf Pg (z k) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2 +
      4 * γ * lam k * β * ‖gradient h (RelaxedPRS.StrongCvx.xg Pg (z k)) - gradient h (RelaxedPRS.StrongCvx.xg Pg zs)‖ ^ 2 +
      4 * lam k * (1 - lam k) * ‖RelaxedPRS.StrongCvx.xf Pf Pg (z k) - RelaxedPRS.StrongCvx.xg Pg (z k)‖ ^ 2 ≤
      ‖z k - zs‖ ^ 2 - ‖z (k + 1) - zs‖ ^ 2 := by sorry
end RelaxedPRS.Linear
