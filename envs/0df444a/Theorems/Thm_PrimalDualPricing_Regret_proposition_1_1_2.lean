-- Prove2me | Theorems.Thm_PrimalDualPricing_Regret_proposition_1_1_2
-- name    : PrimalDualPricing.Regret.proposition_1_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:22:28.554382+00:00
-- url     : https://prove2.me/theorems/20da8ead-97d6-49f9-b554-f753ae2e3974
-- title:
--   Proposition 1.1–1.2, p. 6 — $\mathcal P_m$ increasing and Lipschitz; $\mathcal R_m$ decreasing, convex, $\mathcal R_m'(z)=-d_m(\mathcal P_m(z))$
-- statement:
--   Let the demand functions $d_m$ satisfy Assumption 1 on the price domain $[0,p_\infty]$, and let
--   $$\mathcal R_m(z)=\max_{p\in[0,p_\infty]}d_m(p)(p-z),\qquad \mathcal P_m(z)=\operatorname*{argmax}_{p\in[0,p_\infty]}d_m(p)(p-z).$$
--   Then for every type $m$:
--   1. $\mathcal P_m(z)$ is increasing in $z$, and it is Lipschitz continuous;
--   2. $\mathcal R_m(z)$ is decreasing and convex in $z$, and differentiable at every $z$ with
--   $$\mathcal R_m'(z)=-d_m(\mathcal P_m(z)).$$
--
--   Part 2 gives the derivative of the dual function, $g'(z)=c-T\sum_m d_m(\mathcal P_m(z))$, which the analysis uses for the optimality of $z^*$.
--
--   **Formalization Note** "Increasing" and "decreasing" are weak (`Monotone`, `Antitone`): $\mathcal P_m$ is constant at an endpoint of $[0,p_\infty]$ for extreme $z$. The page's "$\mathcal P'_m(z)$ is bounded" is stated as a Lipschitz bound, because $\mathcal P_m$ has kinks where the maximizer reaches $0$ or $p_\infty$. The page prints $\mathcal R_m'(z)=-\sum_{m=1}^M d_m(\mathcal P_m(z))$, which reuses the index $m$. The proof (p. 25) and footnote 4 (p. 9) use $-d_m(\mathcal P_m(z))$, the form stated here. Part 3 (twice differentiability and strict convexity of $g$) fails globally, since $g$ is affine once every $\mathcal P_m(z)=p_\infty$, and is not stated; Remark 2 assumes the bounds the analysis needs.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 6, Proposition 1, parts 1–2

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_Model

namespace PrimalDualPricing.Regret

/-- Proposition 1, parts 1 and 2 (Chen–Gallego, arXiv:1812.09234v3, p. 6), under Assumption 1
(`Model`), for every type `m`:
1. `𝒫_m(z)` is (weakly) increasing in `z`, and it is Lipschitz (the page's "`𝒫'_m(z)` is bounded"; `𝒫_m`
   has kinks where the maximizer reaches `0` or `p_∞`, so the bound is stated as a Lipschitz bound);
2. `ℛ_m(z)` is (weakly) decreasing and convex in `z`, with derivative `ℛ'_m(z) = −d_m(𝒫_m(z))` at every
   `z` (the page prints `−∑_{m=1}^M d_m(𝒫_m(z))`, reusing the index `m`; the derivative of one type's
   `ℛ_m` is that type's demand). -/
theorem proposition_1_1_2 {M : ℕ} (μ : Model M) (m : Fin M) :
    (Monotone (μ.P m) ∧ ∃ L : NNReal, LipschitzWith L (μ.P m)) ∧
    (Antitone (μ.Rm m) ∧ ConvexOn ℝ Set.univ (μ.Rm m) ∧
      ∀ z : ℝ, HasDerivAt (μ.Rm m) (-(μ.d m (μ.P m z))) z) := by sorry

end PrimalDualPricing.Regret
