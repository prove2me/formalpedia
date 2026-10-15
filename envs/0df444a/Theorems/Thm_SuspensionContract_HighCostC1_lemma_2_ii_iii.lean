-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC1_lemma_2_ii_iii
-- name    : SuspensionContract.HighCostC1.lemma_2_ii_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:02.54923+00:00
-- url     : https://prove2.me/theorems/4c5f38e4-9774-44da-a3a7-ab9523cbf592
-- title:
--   Lemma 2(ii)–(iii), p. 21 — 𝒱_w̃ is increasing and concave on [0, w̃), decreasing in w̃, with slope increasing in w̃
-- statement:
--   Assume the standing assumptions and let $\mathcal V_{\tilde w}$ be the concavified function of Lemma 2(ii): the tangent line of $V_{\tilde w}$ at $\check w(\tilde w)$ on $[0,\check w(\tilde w))$, and $V_{\tilde w}(w\wedge\tilde w)$ on $[\check w(\tilde w),\infty)$. Then:
--
--   1. for every $\tilde w\in(0,\bar w)$, $\mathcal V_{\tilde w}$ is strictly increasing and concave on $[0,\tilde w)$;
--   2. for all $0<\tilde w_1<\tilde w_2<\bar w$ and every $w\in[0,\tilde w_1)$,
--   $$\mathcal V_{\tilde w_1}(w)>\mathcal V_{\tilde w_2}(w)\qquad\text{and}\qquad\mathcal V_{\tilde w_1}'(w)<\mathcal V_{\tilde w_2}'(w).$$
--
--   $\mathcal V_{\hat{\mathrm w}}$ is the working-state value function of Propositions 2 and 3, and part 2 is what makes $\hat{\mathrm w}$ of Lemma 3 unique.
--
--   **Formalization Note** "Increasing" is strict; $\mathcal V'$ is the derivative within $\mathbb R_+$ (right derivative at $0$).
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. 21, Lemma 2(ii)–(iii)

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC1_DelayODE

namespace SuspensionContract.HighCostC1
theorem lemma_2_ii_iii (P : Params) (hP : P.Standing) :
    (∀ wt ∈ Set.Ioo 0 P.wbar,
      StrictMonoOn (P.calV wt) (Set.Ico 0 wt) ∧ ConcaveOn ℝ (Set.Ico 0 wt) (P.calV wt)) ∧
      ∀ wt₁ wt₂, 0 < wt₁ → wt₁ < wt₂ → wt₂ < P.wbar → ∀ w ∈ Set.Ico 0 wt₁,
        P.calV wt₂ w < P.calV wt₁ w ∧ d1 (P.calV wt₁) w < d1 (P.calV wt₂) w := by sorry
end SuspensionContract.HighCostC1
