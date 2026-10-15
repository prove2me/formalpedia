-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC1_lemma_3
-- name    : SuspensionContract.HighCostC1.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:12.214944+00:00
-- url     : https://prove2.me/theorems/58e5d742-629f-4a6c-bb50-fafb5b4d6044
-- title:
--   Lemma 3, p. 21 — under Condition 1 a unique ŵ ∈ [0, w̄) has 𝒱_ŵ(0) = v̲; if w̌(ŵ) > 0 then 𝒱′_ŵ(0) = 𝒱′_ŵ(w̌(ŵ)) > 1
-- statement:
--   Assume the standing assumptions and Condition 1 ($\mu\ge\rho-r$ or $R<\hat R$). Then there is exactly one $\hat{\mathrm w}\in[0,\bar w)$ with
--
--   $$\mathcal V_{\hat{\mathrm w}}(0)=\underline v,$$
--
--   where $\mathcal V_{\hat{\mathrm w}}$ is the concavified function of Lemma 2 with $\hat{\mathrm w}$ in place of $\tilde w$. Moreover, if $\check w(\hat{\mathrm w})>0$, then $\mathcal V_{\hat{\mathrm w}}'(0)=\mathcal V_{\hat{\mathrm w}}'(\check w(\hat{\mathrm w}))>1$.
--
--   The point $\hat{\mathrm w}$ (upright w, distinct from the payment threshold $\hat w$ of Definition 1) is the $K$-independent upper bound on promised utility in the high-switching-cost regime.
--
--   **Formalization Note** The second part is stated for $\hat{\mathrm w}$ defined as the infimum of the solution set; by the first part that set is a singleton. $\mathcal V'$ is the derivative within $\mathbb R_+$.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. 21, Lemma 3

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC1_DelayODE

namespace SuspensionContract.HighCostC1
theorem lemma_3 (P : Params) (hP : P.Standing) (h1 : P.Condition1) :
    (∃! w, 0 ≤ w ∧ w < P.wbar ∧ P.calV w 0 = P.vlow) ∧
      (0 < P.wcheck P.what →
        d1 (P.calV P.what) 0 = d1 (P.calV P.what) (P.wcheck P.what) ∧
          1 < d1 (P.calV P.what) 0) := by sorry
end SuspensionContract.HighCostC1
