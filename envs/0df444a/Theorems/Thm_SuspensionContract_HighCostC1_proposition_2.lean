-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC1_proposition_2
-- name    : SuspensionContract.HighCostC1.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:21.325976+00:00
-- url     : https://prove2.me/theorems/cec7ac93-6043-4adc-b0d1-55a28bd4f7db
-- title:
--   Proposition 2, p. 22 — under Condition 1 and K ≥ V̄(ŵ) − v̲, V_I = 𝒱_ŵ and V_∅ = v̲ satisfy (20)–(22)
-- statement:
--   Assume the standing assumptions and Condition 1, let $\hat{\mathrm w}$ be the upper bound of Lemma 3, and suppose the switching cost is large:
--
--   $$K\ \ge\ \bar V(\hat{\mathrm w})-\underline v,\qquad \bar V(w)=\frac{R\mu-c-(\rho-r)w}{r}.$$
--
--   Then the functions $V_I(w)=\mathcal V_{\hat{\mathrm w}}(w)$ and $V_\emptyset(w)=\underline v$ satisfy the optimality condition (20)–(22): $(\mathcal A_IV_I)(w)\ge0$ and $(\mathcal A_\emptyset V_\emptyset)(w)\ge0$ for $w>0$, $0\le V_I(w)-V_\emptyset(w)\le K$ for $w\ge0$, and $V_I(0)\ge\underline v$, $V_\emptyset(0)\ge\underline v$.
--
--   Through the paper's verification theorem this shows that, when restarting work is this expensive, never hiring the agent is optimal.
--
--   **Formalization Note** The proposition's second claim, $U(\underline\Gamma)=\underline v$ for the never-hire contract (16), concerns the contract model, which is not formalized, and is not stated. Inequality (20) is required for $w>0$ (see the Setting file).
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. 22, Proposition 2 (first claim)

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC1_DelayODE

namespace SuspensionContract.HighCostC1
theorem proposition_2 (P : Params) (hP : P.Standing) (h1 : P.Condition1)
    (hK : P.VbarFn P.what - P.vlow ≤ P.K) :
    P.OptCond (P.calV P.what) (fun _ => P.vlow) := by sorry
end SuspensionContract.HighCostC1
