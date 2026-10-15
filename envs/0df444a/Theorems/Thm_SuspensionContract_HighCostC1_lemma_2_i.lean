-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC1_lemma_2_i
-- name    : SuspensionContract.HighCostC1.lemma_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:58.471983+00:00
-- url     : https://prove2.me/theorems/f84f347d-bf29-4280-bbf6-1bdfe5319231
-- title:
--   Lemma 2(i), p. 21 — V″_w̃ > 0 on [0, w̌(w̃)), V″_w̃ < 0 on (w̌(w̃), w̃), and w̌(w̃) ≤ (1 − r/ρ)β
-- statement:
--   Assume the standing assumptions, let $\tilde w\in(0,\bar w)$, let $V_{\tilde w}$ solve (25)–(26), and let $\check w(\tilde w)$ be the supremum of the $x\in[0,\tilde w]$ such that $V_{\tilde w}''>0$ on $[0,x)$. Then $\check w(\tilde w)\in[0,\tilde w)$,
--
--   $$V_{\tilde w}''(w)<0\ \text{ for } w\in(\check w(\tilde w),\tilde w),\qquad V_{\tilde w}''(w)>0\ \text{ for } w\in[0,\check w(\tilde w)),$$
--
--   and $\check w(\tilde w)\le(1-r/\rho)\beta$.
--
--   So $V_{\tilde w}$ is convex up to $\check w(\tilde w)$ and strictly concave after it, which is what makes the concavification of Lemma 2(ii) necessary.
--
--   **Formalization Note** $V''$ is the second derivative within $\mathbb R_+$ (right derivative at $0$). Because $\check w(\tilde w)$ is defined by a supremum rather than as a sign-change point, all four claims carry content.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. 21, Lemma 2(i)

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC1_DelayODE

namespace SuspensionContract.HighCostC1
theorem lemma_2_i (P : Params) (hP : P.Standing) (wt : ℝ) (hwt : wt ∈ Set.Ioo 0 P.wbar) :
    P.wcheck wt ∈ Set.Ico 0 wt ∧
      (∀ w ∈ Set.Ioo (P.wcheck wt) wt, d2 (P.Vt wt) w < 0) ∧
      (∀ w ∈ Set.Ico 0 (P.wcheck wt), 0 < d2 (P.Vt wt) w) ∧
      P.wcheck wt ≤ (1 - P.r / P.ρ) * P.β := by sorry
end SuspensionContract.HighCostC1
