-- Prove2me | Theorems.Thm_PolicyGradTheory_ChainLB_chain_vanishing_gradients
-- name    : PolicyGradTheory.ChainLB.chain_vanishing_gradients
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:32:28.971974+00:00
-- url     : https://prove2.me/theorems/02262943-0f05-4164-a644-0e2f2a096754
-- title:
--   Proposition 4.1 — exponentially small low-order derivatives at suboptimal parameters
-- statement:
--   Consider the deterministic chain with $H+2$ states, $H\ge1$, discount $\gamma=H/(H+1)$, and the direct policy parameterization. Suppose every free coordinate of $\theta$ lies strictly between zero and one and every forward-action coordinate is below $1/4$. Let $\pi^\star$ be an optimal policy. For every integer $k\ge0$ such that $k\le H/(40\log(2H))-1$,
--   $$\|\nabla_\theta^k V^{\pi_\theta}(s_0)\|_{\mathrm{op}}\le(1/3)^{H/4}.$$
--   Moreover,
--   $$V^\star(s_0)-V^{\pi_\theta}(s_0)\ge\frac{H+1}{8}-\frac{(H+1)^2}{3^H}.$$
--
--   The proposition exhibits parameters at which low-order derivatives reveal little about a substantial value gap.
--
--   **Formalization Note** Parameters have three coordinates per interior state, with the fourth action's probability determined by the first three. The derivative norm is the multilinear operator norm induced by Euclidean norms. The paper's coordinate hypotheses do not themselves enforce that the fourth probability is nonnegative; the value expression depends only on the forward coordinates.
-- source:
--   arXiv:1908.00261v5, Proposition 4.1, p. 16

import Mathlib
import Definitions.Def_PolicyGradTheory_ChainLB_Chain
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy

namespace PolicyGradTheory.ChainLB

open FoundationsML.ReinforcementLearning

/-- Proposition 4.1, p. 16: exponentially small derivatives at a substantially suboptimal parameter. -/
theorem chain_vanishing_gradients (H : ℕ) (hH : 1 ≤ H)
    (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hθ : ∀ i j, 0 < θ (i, j) ∧ θ (i, j) < 1)
    (hθ1 : ∀ i, θ (i, (0 : Fin 3)) < 1 / 4)
    (πstar : Fin (H + 2) → Fin 4 → ℝ) (hπstar : IsPolicy πstar)
    (hopt : IsOptimalPolicy πstar (chainP H) (chainR H) (chainGamma H)) :
    (∀ k : ℕ, (k : ℝ) ≤ (H : ℝ) / (40 * Real.log (2 * H)) - 1 →
      ‖iteratedFDeriv ℝ k (chainValue H) θ‖ ≤ (1 / 3 : ℝ) ^ ((H : ℝ) / 4)) ∧
    (H + 1 : ℝ) / 8 - (H + 1 : ℝ) ^ 2 / (3 : ℝ) ^ H ≤
      PolicyValue πstar (chainP H) (chainR H) (chainGamma H) 0 - chainValue H θ := by sorry

end PolicyGradTheory.ChainLB
