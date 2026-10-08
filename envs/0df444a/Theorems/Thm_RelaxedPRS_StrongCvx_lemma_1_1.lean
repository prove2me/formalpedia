-- Prove2me | Theorems.Thm_RelaxedPRS_StrongCvx_lemma_1_1
-- name    : RelaxedPRS.StrongCvx.lemma_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:47.998328+00:00
-- url     : https://prove2.me/theorems/9cc623c1-b70b-42ab-9473-58ad77f2f2ea
-- title:
--   Lemma 1.1 — proximal subgradients and relaxed PRS identities
-- statement:
--   For closed, proper, convex $f,g$ on a real Hilbert space and $\gamma>0$, let $x_g=\operatorname{prox}_{\gamma g}(z)$ and $x_f=\operatorname{prox}_{\gamma f}(2x_g-z)$. The vectors $\widetilde\nabla g(x_g)=\gamma^{-1}(z-x_g)$ and $\widetilde\nabla f(x_f)=\gamma^{-1}(2x_g-z-x_f)$ belong to $\partial g(x_g)$ and $\partial f(x_f)$, respectively. They satisfy
--   $$x_g=z-\gamma\widetilde\nabla g(x_g),\qquad x_f=x_g-\gamma\widetilde\nabla g(x_g)-\gamma\widetilde\nabla f(x_f),$$
--   and, for the relaxed step $z^+=((1-\lambda)I+\lambda T_{\mathrm{PRS}})z$,
--   $$z^+-z=2\lambda(x_f-x_g)=-2\lambda\gamma(\widetilde\nabla g(x_g)+\widetilde\nabla f(x_f)).$$
--   These identities connect the operator iteration to objective and subgradient inequalities.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 7, Lemma 1.1, (1.11)–(1.12)

import Mathlib
import Definitions.Def_RelaxedPRS_StrongCvx_Setting

open scoped InnerProductSpace

namespace RelaxedPRS.StrongCvx

/-- Lemma 1.1, p. 7: the proximal subgradients and the identities (1.11)–(1.12). -/
theorem lemma_1_1 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg)
    (lam : ℝ) (z : H) :
    gtG γ Pg z ∈ MoreauProx.Characterization.subgrad g (xg Pg z) ∧
    gtF γ Pf Pg z ∈ MoreauProx.Characterization.subgrad f (xf Pf Pg z) ∧
    xg Pg z = z - γ • gtG γ Pg z ∧
    xf Pf Pg z = xg Pg z - γ • gtG γ Pg z - γ • gtF γ Pf Pg z ∧
    Tlam Pf Pg lam z - z = (2 * lam) • (xf Pf Pg z - xg Pg z) ∧
    Tlam Pf Pg lam z - z = -(2 * lam * γ) • (gtG γ Pg z + gtF γ Pf Pg z) := by sorry

end RelaxedPRS.StrongCvx
