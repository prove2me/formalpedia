-- Prove2me | Theorems.Thm_RelaxedPRS_BestIter_lemma_1_1
-- name    : RelaxedPRS.BestIter.lemma_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:07.141619+00:00
-- url     : https://prove2.me/theorems/93ecb525-3f01-43dc-af17-795024a69b1a
-- title:
--   Lemma 1.1, p. 7 — prox subgradients and the identities (1.11)–(1.12) of a relaxed PRS step
-- statement:
--   Let $f, g : \mathcal H \to (-\infty,\infty]$ be closed, proper and convex, $\gamma > 0$, $\lambda \in \mathbb R$ and $z \in \mathcal H$. Let $x_g = \mathbf{prox}_{\gamma g}(z)$, $x_f = \mathbf{prox}_{\gamma f}(\mathbf{refl}_{\gamma g}(z))$, and let
--   $\widetilde\nabla g(x_g) = \frac1\gamma(z - x_g)$, $\widetilde\nabla f(x_f) = \frac1\gamma(\mathbf{refl}_{\gamma g}(z) - x_f)$. Then
--   1. $\widetilde\nabla g(x_g) \in \partial g(x_g)$ and $\widetilde\nabla f(x_f) \in \partial f(x_f)$;
--   2. (1.11): $x_g = z - \gamma\widetilde\nabla g(x_g)$ and $x_f = x_g - \gamma\widetilde\nabla g(x_g) - \gamma\widetilde\nabla f(x_f)$;
--   3. (1.12): with $z^+ = (T_{\mathrm{PRS}})_\lambda(z)$,
--   $$z^+ - z = 2\lambda(x_f - x_g) = -2\lambda\gamma\big(\widetilde\nabla g(x_g) + \widetilde\nabla f(x_f)\big).$$
--
--   The lemma expresses a relaxed PRS step through subgradients of $f$ and $g$; it is the algebra behind every fundamental inequality of the paper.
--
--   **Formalization Note** The paper's notation $\widetilde\nabla$ ("a subgradient", Proposition 1.1 Part 1) is encoded by the explicit difference quotients, so the memberships in part 1 are stated explicitly; without them the identities would be pure algebra.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 7, Lemma 1.1, (1.11)–(1.12); p. 6, Proposition 1.1 Part 1

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_RelaxedPRS_BestIter_Setting
open ThreeOpSplitting.ConvexRates MoreauProx.Characterization Filter

namespace RelaxedPRS.BestIter

theorem lemma_1_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H) (hPf : IsProx γ f Pf) (hPg : IsProx γ g Pg)
    (t : ℝ) (z : H) :
    RelaxedPRS.StrongCvx.gtG γ Pg z ∈ subgrad g (xg Pg z) ∧
    RelaxedPRS.StrongCvx.gtF γ Pf Pg z ∈ subgrad f (RelaxedPRS.StrongCvx.xf Pf Pg z) ∧
    xg Pg z = z - γ • RelaxedPRS.StrongCvx.gtG γ Pg z ∧
    RelaxedPRS.StrongCvx.xf Pf Pg z = xg Pg z - γ • RelaxedPRS.StrongCvx.gtG γ Pg z - γ • RelaxedPRS.StrongCvx.gtF γ Pf Pg z ∧
    RelaxedPRS.StrongCvx.Tlam Pf Pg t z - z = (2 * t) • (RelaxedPRS.StrongCvx.xf Pf Pg z - xg Pg z) ∧
    RelaxedPRS.StrongCvx.Tlam Pf Pg t z - z = -(2 * t * γ) • (RelaxedPRS.StrongCvx.gtG γ Pg z + RelaxedPRS.StrongCvx.gtF γ Pf Pg z) := by sorry

end RelaxedPRS.BestIter
