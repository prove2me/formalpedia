-- Prove2me | Theorems.Thm_RelaxedPRS_Linear_eq_2_1
-- name    : RelaxedPRS.Linear.eq_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:22:54.983405+00:00
-- url     : https://prove2.me/theorems/16f4b53e-0863-4db1-9951-a3938fb23e26
-- title:
--   (2.1) — auxiliary-term decrease inequality
-- statement:
--   Suppose $f,g$ are proper closed convex functions, with nonnegative strong-convexity and gradient-regularity parameters $\mu_f,\beta_f,\mu_g,\beta_g$. Let $z^k$ follow relaxed PRS with $\gamma>0$ and $0<\lambda_k\le1$, and let $z^*$ be a fixed point of $T_{\rm PRS}$. Set $x^*=P_gz^*$ and let $S_f^k,S_g^k$ be the terms of (1.14) at the auxiliary proximal points and their selected proximal subgradients, relative to $x^*$ and the subgradients at $z^*$. For every $k\ge0$,
--
--   $$8\gamma\lambda_k(S_f^k+S_g^k)\le\|z^k-z^*\|^2-\|z^{k+1}-z^*\|^2+\left(1-\frac1{\lambda_k}\right)\|z^{k+1}-z^k\|^2.$$
--
--   This is the one-step decrease inequality used by each regularity case in the paper's rate analysis.
--
--   **Formalization Note** When a parameter $\beta$ is positive, its function is assumed real valued with a $(1/\beta)$-Lipschitz gradient; when $\beta=0$, no differentiability is imposed.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 8, Theorem 2.1, (2.1)

import Mathlib
import Definitions.Def_RelaxedPRS_Linear_Setting

namespace RelaxedPRS.Linear

/-- (2.1) of Theorem 2.1, p. 8: one-step auxiliary-term bound. -/
theorem eq_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg)
    (lam : ℕ → ℝ) (hlam : ∀ k, 0 < lam k ∧ lam k ≤ 1)
    (z : ℕ → H) (hz : RelaxedPRS.StrongCvx.IsPRSRun Pf Pg lam z)
    (zs : H) (hzs : RelaxedPRS.StrongCvx.TPRS Pf Pg zs = zs)
    (μf βf μg βg : ℝ)
    (hμf : 0 ≤ μf) (hβf : 0 ≤ βf) (hμg : 0 ≤ μg) (hβg : 0 ≤ βg)
    (hscf : RelaxedPRS.StrongCvx.IsStrongCvxE μf f) (hscg : RelaxedPRS.StrongCvx.IsStrongCvxE μg g)
    (hlf : 0 < βf → RelaxedPRS.StrongCvx.HasLipGrad βf f)
    (hlg : 0 < βg → RelaxedPRS.StrongCvx.HasLipGrad βg g) :
    let Sf : ℕ → ℝ := fun k =>
      RelaxedPRS.StrongCvx.auxS μf βf (RelaxedPRS.StrongCvx.xf Pf Pg (z k)) (RelaxedPRS.StrongCvx.xg Pg zs)
        (RelaxedPRS.StrongCvx.gtF γ Pf Pg (z k)) (RelaxedPRS.StrongCvx.gtF γ Pf Pg zs)
    let Sg : ℕ → ℝ := fun k =>
      RelaxedPRS.StrongCvx.auxS μg βg (RelaxedPRS.StrongCvx.xg Pg (z k)) (RelaxedPRS.StrongCvx.xg Pg zs)
        (RelaxedPRS.StrongCvx.gtG γ Pg (z k)) (RelaxedPRS.StrongCvx.gtG γ Pg zs)
    ∀ k, 8 * γ * lam k * (Sf k + Sg k) ≤
      ‖z k - zs‖ ^ 2 - ‖z (k + 1) - zs‖ ^ 2 +
        (1 - 1 / lam k) * ‖z (k + 1) - z k‖ ^ 2 := by sorry
end RelaxedPRS.Linear
