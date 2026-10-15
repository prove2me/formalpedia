-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC2_proposition_4_i
-- name    : SuspensionContract.HighCostC2.proposition_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:22.433976+00:00
-- url     : https://prove2.me/theorems/10a06585-556f-4aa2-9150-64ad96669b28
-- title:
--   Proposition 4, first part, pp. 23–24 — under Condition 2 and K > V̄ − v̲, (31) and V_∅ ≡ v̲ satisfy (20)–(22)
-- statement:
--   Assume the standing assumptions of the model and **Condition 2**: $\mu<\rho-r$ and $R\ge\hat R$. If the switching cost satisfies
--   $$K>\bar V-\underline v,$$
--   then the working-state function $V_I$ of (31) — the line from $\underline v$ at $w=0$ to $\bar V$ at $w=\bar w$, constant $\bar V$ beyond — and the constant suspension-state function $V_\emptyset(w)=\underline v$ satisfy the optimality condition (20)–(22): for every $w>0$, $(\mathcal A_IV_I)(w)\ge0$ and $(\mathcal A_\emptyset V_\emptyset)(w)\ge0$; for every $w\ge0$, $0\le V_I(w)-V_\emptyset(w)\le K$; and $V_I(0)\ge\underline v$, $V_\emptyset(0)\ge\underline v$.
--
--   Via the paper's verification theorem this certifies that, for very high switching cost, the principal's value never exceeds $\underline v$, i.e. not hiring the agent is optimal.
--
--   **Formalization Note.** $f'$ in $\mathcal A_I,\mathcal A_\emptyset$ is the left derivative, so at the kink $w=\bar w$ it is the slope $(\bar V-\underline v)/\bar w$, as the paper's proof uses. Inequality (20) is required for $w>0$; for these functions it also holds at $w=0$ with right derivatives, but the formal operator is not evaluated there (see the Setting).
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, pp. 23–24, Proposition 4 (case K > V̄ − v̲); proof EC.3.6, p. ec31, first paragraph

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Setting

namespace SuspensionContract.HighCostC2
theorem proposition_4_i (P : Params) (hP : P.Standing) (h2 : P.Condition2)
    (hK : P.Vbar - P.vlow < P.K) : P.OptCond P.VI31 (fun _ => P.vlow) := by sorry
end SuspensionContract.HighCostC2
