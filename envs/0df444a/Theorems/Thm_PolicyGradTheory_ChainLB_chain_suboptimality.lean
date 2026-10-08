-- Prove2me | Theorems.Thm_PolicyGradTheory_ChainLB_chain_suboptimality
-- name    : PolicyGradTheory.ChainLB.chain_suboptimality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:32:18.759962+00:00
-- url     : https://prove2.me/theorems/325c6917-18fa-4e3e-8d90-4707fca6eec9
-- title:
--   Appendix B.2, p. 59 — lower optimal value and upper chain value
-- statement:
--   On the Figure 2 chain with $H\ge1$, let $\pi^\star$ be an optimal policy and let $\theta$ satisfy the hypotheses of Proposition 4.1. Then
--   $$V^\star(s_0)\ge\frac{H+1}{8},\qquad V^{\pi_\theta}(s_0)\le\frac{(H+1)^2}{3^H}.$$
--
--   Together these estimates yield the quantitative value gap in Proposition 4.1.
--
--   **Formalization Note** The paper writes $\gamma^{H+2}/(1-\gamma)$ for the always-forward policy. The first reward is actually received at time $H+1$, giving $\gamma^{H+1}/(1-\gamma)$; the weaker displayed lower bound still follows.
-- source:
--   arXiv:1908.00261v5, App. B.2, proof of Proposition 4.1, p. 59

import Mathlib
import Definitions.Def_PolicyGradTheory_ChainLB_Chain
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy

namespace PolicyGradTheory.ChainLB

open FoundationsML.ReinforcementLearning

/-- Appendix B.2, p. 59: the optimal value is large while the chain policy's value is small. -/
theorem chain_suboptimality (H : ℕ) (hH : 1 ≤ H)
    (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hθ : ∀ i j, 0 < θ (i, j) ∧ θ (i, j) < 1)
    (hθ1 : ∀ i, θ (i, (0 : Fin 3)) < 1 / 4)
    (πstar : Fin (H + 2) → Fin 4 → ℝ) (hπstar : IsPolicy πstar)
    (hopt : IsOptimalPolicy πstar (chainP H) (chainR H) (chainGamma H)) :
    (H + 1 : ℝ) / 8 ≤ PolicyValue πstar (chainP H) (chainR H) (chainGamma H) 0 ∧
    chainValue H θ ≤ (H + 1 : ℝ) ^ 2 / (3 : ℝ) ^ H := by sorry

end PolicyGradTheory.ChainLB
