-- Prove2me | Theorems.Thm_RelaxedPRS_Linear_theorem_4_3
-- name    : RelaxedPRS.Linear.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:09.58098+00:00
-- url     : https://prove2.me/theorems/ded36067-74da-4a12-88c4-753e35cf4699
-- title:
--   Theorem 4.3 — mixed regularity gives linear contraction
-- statement:
--   Let $f,g:H\to(-\infty,+\infty]$ be proper closed convex functions on a real Hilbert space. Let $\gamma>0$, let $z^k$ follow relaxed PRS with $0<\lambda_k\le1$, and let $z^*$ be a fixed point of $T_{\rm PRS}$. Suppose either $g$ has a $(1/\beta)$-Lipschitz gradient and $f$ is $\mu$-strongly convex, or $f$ has that gradient regularity and $g$ is $\mu$-strongly convex, with $\mu,\beta>0$. Define
--
--   $$C(\lambda)=\left(1-\frac{4\lambda}{3}\min\left\{\gamma\mu,\frac\beta\gamma,1-\lambda\right\}\right)^{1/2},\qquad 0\le\lambda\le1.$$
--
--   In each of the two cases, for all $k\ge0$,
--
--   $$\|z^{k+1}-z^*\|\le C(\lambda_k)\|z^k-z^*\|.$$
--
--   This is the paper's mixed-regularity linear contraction theorem, covering both readings of “respectively.”
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 16, Theorem 4.3

import Mathlib
import Definitions.Def_RelaxedPRS_Linear_Setting

namespace RelaxedPRS.Linear

/-- Theorem 4.3, p. 16: linear contraction when regularity is split across f and g. -/
theorem theorem_4_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg)
    (lam : ℕ → ℝ) (hlam : ∀ k, 0 < lam k ∧ lam k ≤ 1)
    (z : ℕ → H) (hz : RelaxedPRS.StrongCvx.IsPRSRun Pf Pg lam z)
    (zs : H) (hzs : RelaxedPRS.StrongCvx.TPRS Pf Pg zs = zs)
    (μ β : ℝ) (hμ : 0 < μ) (hβ : 0 < β) :
    (RelaxedPRS.StrongCvx.HasLipGrad β g → RelaxedPRS.StrongCvx.IsStrongCvxE μ f →
      ∀ k, ‖z (k + 1) - zs‖ ≤ C43 γ μ β (lam k) * ‖z k - zs‖) ∧
    (RelaxedPRS.StrongCvx.HasLipGrad β f → RelaxedPRS.StrongCvx.IsStrongCvxE μ g →
      ∀ k, ‖z (k + 1) - zs‖ ≤ C43 γ μ β (lam k) * ‖z k - zs‖) := by sorry
end RelaxedPRS.Linear
