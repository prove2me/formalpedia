-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC2_proposition_4_ii
-- name    : SuspensionContract.HighCostC2.proposition_4_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:27.084824+00:00
-- url     : https://prove2.me/theorems/423060c9-e4ce-4a29-982e-ca228124edec
-- title:
--   Proposition 4, second part, p. 24 — under Condition 2 and K̄₂ < K ≤ V̄ − v̲, (31) and (32) satisfy (20)–(22)
-- statement:
--   Assume the standing assumptions of the model and **Condition 2**: $\mu<\rho-r$ and $R\ge\hat R$. If the switching cost satisfies
--   $$\bar K_2<K\le\bar V-\underline v,\qquad \bar K_2=\bar V-\underline v-\bar w,$$
--   then the working-state function $V_I$ of (31) and the suspension-state function $V_\emptyset$ of (32) — the line from $\underline v$ at $w=0$ to $\bar V-K$ at $w=\bar w$, constant $\bar V-K$ beyond — satisfy the optimality condition (20)–(22): for every $w>0$, $(\mathcal A_IV_I)(w)\ge0$ and $(\mathcal A_\emptyset V_\emptyset)(w)\ge0$; for every $w\ge0$, $0\le V_I(w)-V_\emptyset(w)\le K$; and $V_I(0)\ge\underline v$, $V_\emptyset(0)\ge\underline v$.
--
--   Together with the first part, this covers the whole not-hiring region $K>\bar K_2$ under Condition 2.
--
--   **Formalization Note.** $f'$ in $\mathcal A_I,\mathcal A_\emptyset$ is the left derivative (the slopes at the kink $w=\bar w$ are $(\bar V-\underline v)/\bar w$ and $(\bar V-\underline v-K)/\bar w$). Inequality (20) is required for $w>0$ (see the Setting).
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. 24, Proposition 4 (case K̄₂ < K ≤ V̄ − v̲); proof EC.3.6, p. ec31, "Second, …"

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Setting

namespace SuspensionContract.HighCostC2
theorem proposition_4_ii (P : Params) (hP : P.Standing) (h2 : P.Condition2)
    (hK1 : P.Kbar2 < P.K) (hK2 : P.K ≤ P.Vbar - P.vlow) : P.OptCond P.VI31 P.V032 := by sorry
end SuspensionContract.HighCostC2
