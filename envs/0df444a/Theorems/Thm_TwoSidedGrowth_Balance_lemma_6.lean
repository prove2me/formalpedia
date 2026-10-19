-- Prove2me | Theorems.Thm_TwoSidedGrowth_Balance_lemma_6
-- name    : TwoSidedGrowth.Balance.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:22.433118+00:00
-- url     : https://prove2.me/theorems/19c6b67d-680f-415a-863e-d9d4aec96ed5
-- title:
--   Lemma 6 (first part), p. 42 — for every market size x > 0, G(γ, x) is strictly concave in the balance γ on [0, 1]
-- statement:
--   In the two-sided growth model under its standing assumptions (in particular Assumption 2, $h''<0$ on $(0,1)$, and continuity of $h$ on $[0,1]$), fix a market size $x>0$. Then the net welfare rate
--   $$\gamma\ \longmapsto\ G(\gamma,x)=(v-c)\,x^{\alpha}h(\gamma)-\bigl(\rho+\beta^s_0\gamma+\beta^d_0(1-\gamma)\bigr)x$$
--   is strictly concave on the balance interval $[0,1]$.
--
--   Strict concavity makes the maximizer of $G(\cdot,x)$ over $[0,1]$ unique, which is what lets the optimal balance be a function $\gamma^*(x)$ of the market size alone.
--
--   **Formalization Note.** Only the first sentence of the printed Lemma 6 is stated; its second sentence (concavity or convexity of $\max_\gamma G(\gamma,x)$ in $x$) is not part of this item. Concavity is on the closed interval $[0,1]$, the constraint set of (13).
-- source:
--   Lian, van Ryzin, Optimal Growth in Two-Sided Markets, SSRN working paper 3310559 (version of 2020-01-16), p. 42, Lemma 6 (first sentence)

import Mathlib
import Definitions.Def_TwoSidedGrowth_Balance_Setting

namespace TwoSidedGrowth.Balance
theorem lemma_6 (M : Model) (hM : M.Standing) (x : ℝ) (hx : 0 < x) :
    StrictConcaveOn ℝ (Set.Icc (0:ℝ) 1) (fun γ => G M γ x) := by sorry
end TwoSidedGrowth.Balance
