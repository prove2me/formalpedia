-- Prove2me | Theorems.Thm_TBSGStrategyIteration_l1_dist_le_card_mul_modCost
-- name    : TBSGStrategyIteration.l1_dist_le_card_mul_modCost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:31:47.623722+00:00
-- url     : https://prove2.me/theorems/df807ebb-087b-4968-909b-646fdced92b1
-- title:
--   Lemma 6.2 — $\|v_{\pi''} - v_\pi\|_1 \le \frac{n}{1-\gamma} (c^\pi)_a$
-- statement:
--   Let $\pi'', \pi$ be strategy profiles with $v_{\pi''} \ge v_\pi$, and let $a = \pi''(i_0)$ be an action of $\pi''$ maximizing the modified cost $c^\pi$ over the actions of $\pi''$. Then
--   $$\|v_{\pi''} - v_\pi\|_1 \le \frac{n}{1-\gamma} \, (c^\pi)_a, \qquad \|x\|_1 = \sum_{i \in S} |x_i|,\ n = |S| .$$
--
--   **Formalization Note.** "$a = \operatorname{argmax}_{\pi''} c^\pi$" is encoded as a state $i_0$ with $(c^\pi)_{\pi''(i)} \le (c^\pi)_{\pi''(i_0)}$ for all $i$; the lemma holds for every maximizer. The 1-norm is written out as a sum.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 9, Lemma 6.2

import Mathlib
import Definitions.Def_TBSGStrategyIteration_modCost

namespace TBSGStrategyIteration

/-- Lemma 6.2: let `π'', π` be strategy profiles with `v_{π''} ≥ v_π`, and let `a = π''(i₀)` be an
action of `π''` maximizing `c^π` over the actions of `π''`. Then
`‖v_{π''} − v_π‖₁ ≤ n/(1 − γ) · (c^π)_a`, with `‖x‖₁ = ∑_i |x_i|` and `n = |S|`. -/
theorem l1_dist_le_card_mul_modCost {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) (π'' π : Profile G)
    (hv : value G π ≤ value G π'') (i₀ : S)
    (hmax : ∀ i : S, modCost G π (π''.act i) ≤ modCost G π (π''.act i₀)) :
    ∑ i, |value G π'' i - value G π i| ≤
      (Fintype.card S : ℝ) / (1 - G.γ) * modCost G π (π''.act i₀) := by sorry

end TBSGStrategyIteration
