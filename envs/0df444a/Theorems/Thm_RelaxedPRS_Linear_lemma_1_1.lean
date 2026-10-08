-- Prove2me | Theorems.Thm_RelaxedPRS_Linear_lemma_1_1
-- name    : RelaxedPRS.Linear.lemma_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:22:58.300582+00:00
-- url     : https://prove2.me/theorems/b72bd839-b11e-4579-b12f-f4a6c8917b38
-- title:
--   Lemma 1.1 — auxiliary proximal points and subgradients
-- statement:
--   Let $f,g$ be proper closed convex functions on a real Hilbert space, let $\gamma>0$, and let $P_f,P_g$ be their $\gamma$-proximal maps. For $z\in H$, set $x_g=P_gz$, $x_f=P_f(2P_gz-z)$, $u_g=(z-x_g)/\gamma$, and $u_f=(2P_gz-z-x_f)/\gamma$. Then $u_g\in\partial g(x_g)$ and $u_f\in\partial f(x_f)$. For each relaxation $t>0$, with $T_t=(1-t)I+tT_{\rm PRS}$,
--
--   $$x_g=z-\gamma u_g,\quad x_f=x_g-\gamma u_g-\gamma u_f,\quad T_tz-z=2t(x_f-x_g)=-2t\gamma(u_g+u_f).$$
--
--   The identities and subgradient memberships connect the operator iteration to the convex objective inequalities.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 7, Lemma 1.1, (1.11)–(1.12)

import Mathlib
import Definitions.Def_RelaxedPRS_Linear_Setting

namespace RelaxedPRS.Linear

/-- Lemma 1.1, p. 7: the selected vectors are subgradients and satisfy (1.11)–(1.12). -/
theorem lemma_1_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg) (t : ℝ) (ht : 0 < t) (z : H) :
    RelaxedPRS.StrongCvx.gtG γ Pg z ∈ MoreauProx.Characterization.subgrad g (RelaxedPRS.StrongCvx.xg Pg z) ∧
    RelaxedPRS.StrongCvx.gtF γ Pf Pg z ∈ MoreauProx.Characterization.subgrad f (RelaxedPRS.StrongCvx.xf Pf Pg z) ∧
    RelaxedPRS.StrongCvx.xg Pg z = z - γ • RelaxedPRS.StrongCvx.gtG γ Pg z ∧
    RelaxedPRS.StrongCvx.xf Pf Pg z = RelaxedPRS.StrongCvx.xg Pg z - γ • RelaxedPRS.StrongCvx.gtG γ Pg z - γ • RelaxedPRS.StrongCvx.gtF γ Pf Pg z ∧
    RelaxedPRS.StrongCvx.Tlam Pf Pg t z - z = (2 * t) • (RelaxedPRS.StrongCvx.xf Pf Pg z - RelaxedPRS.StrongCvx.xg Pg z) ∧
    RelaxedPRS.StrongCvx.Tlam Pf Pg t z - z = -(2 * t * γ) • (RelaxedPRS.StrongCvx.gtG γ Pg z + RelaxedPRS.StrongCvx.gtF γ Pf Pg z) := by sorry
end RelaxedPRS.Linear
