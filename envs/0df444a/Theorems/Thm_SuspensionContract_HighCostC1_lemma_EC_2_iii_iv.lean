-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC1_lemma_EC_2_iii_iv
-- name    : SuspensionContract.HighCostC1.lemma_EC_2_iii_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:57.182809+00:00
-- url     : https://prove2.me/theorems/8ec52d6f-f487-490e-9d28-f49edd8b190b
-- title:
--   Lemma EC.2(iii)–(iv), p. ec23 — V_w̃ is increasing on [0, w̃], and decreases in w̃ while its slope increases in w̃
-- statement:
--   Assume the standing assumptions and let $V_{\tilde w}$ be the solution of the delay ODE (25)–(26). Then:
--
--   1. for every $\tilde w\in[0,\bar w)$, $V_{\tilde w}$ is strictly increasing on $[0,\tilde w]$;
--   2. for all $0<\tilde w_1<\tilde w_2<\bar w$ and every $w\in[0,\tilde w_1)$,
--   $$V_{\tilde w_1}(w)>V_{\tilde w_2}(w)\qquad\text{and}\qquad V_{\tilde w_1}'(w)<V_{\tilde w_2}'(w).$$
--
--   These comparison properties drive the search for the upper bound $\hat{\mathrm w}$ in Lemma 3.
--
--   **Formalization Note** "Increasing" is strict. $V'$ is the derivative within $\mathbb R_+$ (right derivative at $w=0$).
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. ec23, Lemma EC.2(iii)–(iv)

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC1_DelayODE

namespace SuspensionContract.HighCostC1
theorem lemma_EC_2_iii_iv (P : Params) (hP : P.Standing) :
    (∀ wt, 0 ≤ wt → wt < P.wbar → StrictMonoOn (P.Vt wt) (Set.Icc 0 wt)) ∧
      ∀ wt₁ wt₂, 0 < wt₁ → wt₁ < wt₂ → wt₂ < P.wbar → ∀ w ∈ Set.Ico 0 wt₁,
        P.Vt wt₂ w < P.Vt wt₁ w ∧ d1 (P.Vt wt₁) w < d1 (P.Vt wt₂) w := by sorry
end SuspensionContract.HighCostC1
