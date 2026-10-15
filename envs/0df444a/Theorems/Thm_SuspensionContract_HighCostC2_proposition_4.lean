-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC2_proposition_4
-- name    : SuspensionContract.HighCostC2.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:28.537533+00:00
-- url     : https://prove2.me/theorems/447c3bfd-ce70-452e-8b12-c08f830a2434
-- title:
--   Proposition 4, pp. 23–24 — under Condition 2 and K > K̄₂ the linear value functions (31)–(32) satisfy the optimality condition (20)–(22)
-- statement:
--   Consider the principal–agent model with switching cost, under its standing assumptions ($0\le\underline\mu<\mu$, $0<b\le c$, $K>0$, $0<r\le\rho$, $R\Delta\mu>c$), and suppose the parameters satisfy **Condition 2**: $\mu<\rho-r$ and $R\ge\hat R$, with $\hat R$ from (28). Let $\bar w=\beta\mu/\rho$, $\underline v=\underline\mu R/r$, $\bar V=(R\mu-c-(\rho-r)\bar w)/r$ and $\bar K_2=\bar V-\underline v-\bar w$, and let
--   $$V_I(w)=\begin{cases}\underline v+\dfrac{\bar V-\underline v}{\bar w}\,w,& w\in[0,\bar w],\\ \bar V,& w\ge\bar w.\end{cases}\qquad(31)$$
--   Then:
--   1. if $K>\bar V-\underline v$, the pair $V_I$ and $V_\emptyset\equiv\underline v$ satisfies the optimality condition (20)–(22);
--   2. if $\bar K_2<K\le\bar V-\underline v$, the pair $V_I$ and
--   $$V_\emptyset(w)=\begin{cases}\underline v+\dfrac{\bar V-\underline v-K}{\bar w}\,w,& w\in[0,\bar w],\\ \bar V-K,& w\ge\bar w\end{cases}\qquad(32)$$
--   satisfies the optimality condition (20)–(22).
--
--   Here the optimality condition means: $(\mathcal A_IV_I)(w)\ge0$ and $(\mathcal A_\emptyset V_\emptyset)(w)\ge0$ (20), $0\le V_I(w)-V_\emptyset(w)\le K$ (21), and $V_I(0)\ge\underline v$, $V_\emptyset(0)\ge\underline v$ (22), with the operators (18)–(19).
--
--   In the paper these pairs are the certificates which, through the verification Theorem 1, show that under Condition 2 and high switching cost $K>\bar K_2$ it is optimal for the principal never to hire the agent (Theorem 3).
--
--   **Formalization Note.** The derivative in $\mathcal A_I,\mathcal A_\emptyset$ is the left derivative (`derivWithin f (Set.Iic w) w`), as on p. 15 of the paper. Inequality (20) is required for $w>0$; (21) for all $w\ge0$; (22) as printed. At $w=0$ a left derivative on $\mathbb R_+$ does not exist; for the piecewise-linear functions here (20) also holds at $0$ with the right derivative. The stochastic contract model, Theorem 1 and the optimality of not hiring are not formalized.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, pp. 23–24, Proposition 4; proof EC.3.6, p. ec31

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Setting

namespace SuspensionContract.HighCostC2
theorem proposition_4 (P : Params) (hP : P.Standing) (h2 : P.Condition2) :
    (P.Vbar - P.vlow < P.K → P.OptCond P.VI31 (fun _ => P.vlow)) ∧
      (P.Kbar2 < P.K → P.K ≤ P.Vbar - P.vlow → P.OptCond P.VI31 P.V032) := by sorry
end SuspensionContract.HighCostC2
