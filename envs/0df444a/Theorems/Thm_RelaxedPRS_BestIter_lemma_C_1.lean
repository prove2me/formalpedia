-- Prove2me | Theorems.Thm_RelaxedPRS_BestIter_lemma_C_1
-- name    : RelaxedPRS.BestIter.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:09.143656+00:00
-- url     : https://prove2.me/theorems/db1c88b8-a0ac-4d77-a178-ebfbd0a2fd64
-- title:
--   Lemma C.1, p. 35 — zer(∂f + ∂g) = prox_{γg}(Fix T_PRS); at a fixed point x* = x*_g = x*_f solves (1.1) and (C.2)
-- statement:
--   Let $f, g : \mathcal H \to (-\infty,\infty]$ be closed, proper and convex and $\gamma > 0$. Then
--   $$\mathrm{zer}(\partial f + \partial g) = \{\mathbf{prox}_{\gamma g}(z) \mid z \in \mathcal H,\ T_{\mathrm{PRS}} z = z\}, \tag{C.1}$$
--   where $\mathrm{zer}(\partial f + \partial g) = \{x \mid \exists u \in \partial f(x),\ -u \in \partial g(x)\}$. Moreover, if $z^*$ is a fixed point of $T_{\mathrm{PRS}}$ and $x^* = \mathbf{prox}_{\gamma g}(z^*)$, then
--   1. $x^* = x^*_g = x^*_f$, that is, $\mathbf{prox}_{\gamma f}(\mathbf{refl}_{\gamma g}(z^*)) = x^*$;
--   2. $x^*$ minimises $f + g$ (Problem (1.1));
--   3. $\widetilde\nabla g(x^*) = \frac1\gamma(z^* - x^*) \in \partial g(x^*)$ and $-\widetilde\nabla g(x^*) \in \partial f(x^*)$, i.e. $z^* - x^* = \gamma\widetilde\nabla g(x^*) \in \gamma\partial g(x^*)$ (C.2).
--
--   These are the optimality conditions of $T_{\mathrm{PRS}}$: a fixed point delivers a solution of the problem together with matching subgradients of $f$ and $g$ there.
--
--   **Formalization Note** The subdifferential is the published `subgrad`, which also asserts that the function value at the point is finite. The minimisation is stated in `EReal`; neither function takes the value $-\infty$, so the sums are well defined.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 35, Lemma C.1, (C.1)–(C.2); p. 2, (1.1)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_RelaxedPRS_BestIter_Setting
open ThreeOpSplitting.ConvexRates MoreauProx.Characterization Filter

namespace RelaxedPRS.BestIter

theorem lemma_C_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H) (hPf : IsProx γ f Pf) (hPg : IsProx γ g Pg) :
    {x : H | ∃ u ∈ subgrad f x, -u ∈ subgrad g x} = {x : H | ∃ z : H, RelaxedPRS.StrongCvx.TPRS Pf Pg z = z ∧ Pg z = x} ∧
    ∀ zs : H, RelaxedPRS.StrongCvx.TPRS Pf Pg zs = zs →
      RelaxedPRS.StrongCvx.xf Pf Pg zs = xg Pg zs ∧
      (∀ x : H, f (xg Pg zs) + g (xg Pg zs) ≤ f x + g x) ∧
      RelaxedPRS.StrongCvx.gtG γ Pg zs ∈ subgrad g (xg Pg zs) ∧
      -(RelaxedPRS.StrongCvx.gtG γ Pg zs) ∈ subgrad f (xg Pg zs) := by sorry

end RelaxedPRS.BestIter
