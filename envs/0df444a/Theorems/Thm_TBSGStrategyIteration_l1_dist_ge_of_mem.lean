-- Prove2me | Theorems.Thm_TBSGStrategyIteration_l1_dist_ge_of_mem
-- name    : TBSGStrategyIteration.l1_dist_ge_of_mem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:33:28.114358+00:00
-- url     : https://prove2.me/theorems/911250ce-243b-49f9-9892-81a3e00705a9
-- title:
--   Lemma 6.3 — an action of $\pi''$ kept in $\pi'$ keeps $\pi'$ far from $\pi$
-- statement:
--   Let $\pi'', \pi', \pi$ be strategy profiles with $v_{\pi''} \ge v_{\pi'} \ge v_\pi$, let $a = \pi''(i_0)$ maximize $c^\pi$ over the actions of $\pi''$, and suppose $a \in \pi'$ (that is, $\pi'(i) = a$ for some state $i$). Then
--   $$\|v_{\pi'} - v_\pi\|_1 \ge \frac{1-\gamma}{n} \, \|v_{\pi''} - v_\pi\|_1 .$$
--
--   **Formalization Note.** $n \ge 1$ is implied by the existence of $a$, so the division by $n$ is genuine.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 9, Lemma 6.3

import Mathlib
import Definitions.Def_TBSGStrategyIteration_modCost

namespace TBSGStrategyIteration

/-- Lemma 6.3: let `π'', π', π` be strategy profiles with `v_{π''} ≥ v_{π'} ≥ v_π`, let
`a = π''(i₀)` maximize `c^π` over the actions of `π''`, and suppose `a ∈ π'`. Then
`‖v_{π'} − v_π‖₁ ≥ (1 − γ)/n · ‖v_{π''} − v_π‖₁`, with `‖x‖₁ = ∑_i |x_i|` and `n = |S|`. -/
theorem l1_dist_ge_of_mem {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) (π'' π' π : Profile G)
    (h₁ : value G π' ≤ value G π'') (h₂ : value G π ≤ value G π') (i₀ : S)
    (hmax : ∀ i : S, modCost G π (π''.act i) ≤ modCost G π (π''.act i₀))
    (hmem : ∃ i : S, π'.act i = π''.act i₀) :
    (1 - G.γ) / (Fintype.card S : ℝ) * ∑ i, |value G π'' i - value G π i| ≤
      ∑ i, |value G π' i - value G π i| := by sorry

end TBSGStrategyIteration
