-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC1_proposition_3
-- name    : SuspensionContract.HighCostC1.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:54.667881+00:00
-- url     : https://prove2.me/theorems/48cf9e40-f23a-4b31-9a2f-6f17d6bddaa6
-- title:
--   Proposition 3, p. 22 — under Condition 1 and K ∈ [K̄₁, V̄(ŵ) − v̲], V_I = 𝒱_ŵ and V_∅ of (30) satisfy (20)–(22)
-- statement:
--   Assume the standing assumptions and Condition 1, let $\hat{\mathrm w}$ be the upper bound of Lemma 3, $\bar K_1$ the bound (K1), and suppose
--
--   $$\bar K_1\ \le\ K\ \le\ \bar V(\hat{\mathrm w})-\underline v.$$
--
--   Let $(\bar\theta^K,m^K)$ satisfy (29) for this $K$: $\bar\theta^K\in[\check w(\hat{\mathrm w}),\hat{\mathrm w}]$, $m^K\in[0,\mathcal V_{\hat{\mathrm w}}'(0)]$, $\mathcal V_{\hat{\mathrm w}}(\bar\theta^K)=m^K\bar\theta^K+K+\underline v$ and $\mathcal V_{\hat{\mathrm w}}'(\bar\theta^K)=m^K$. Then $V_I(w)=\mathcal V_{\hat{\mathrm w}}(w)$ and
--
--   $$V_\emptyset(w)=\begin{cases}m^Kw+\underline v, & w\in[0,\bar\theta^K],\\ \mathcal V_{\hat{\mathrm w}}(w)-K, & w>\bar\theta^K,\end{cases}$$
--
--   satisfy the optimality condition (20)–(22): $(\mathcal A_IV_I)(w)\ge0$ and $(\mathcal A_\emptyset V_\emptyset)(w)\ge0$ for $w>0$, $0\le V_I(w)-V_\emptyset(w)\le K$ for $w\ge0$, and $V_I(0)\ge\underline v$, $V_\emptyset(0)\ge\underline v$.
--
--   Through the paper's verification theorem this certifies that, for switching costs in this range under Condition 1, the principal's value is at most $V_\emptyset(w)-w$, so not hiring is optimal (Theorem 2(i)).
--
--   **Formalization Note** The statement holds for every pair satisfying (29); the pair is unique, and at the closed end $K=\bar V(\hat{\mathrm w})-\underline v$ (outside Lemma 4's range) it is $(\hat{\mathrm w},0)$. The paper defines (30) on $[0,\hat{\mathrm w}]$; its second branch is extended to $(\bar\theta^K,\infty)$, as the paper's proof (EC.3.5, Case 3) uses. Inequality (20) is required for $w>0$ only: at $w=0$ a left derivative does not exist; (21) and (22) are as printed. $\mathcal V'$ in (29) is the derivative within $\mathbb R_+$; the derivative in $\mathcal A_I,\mathcal A_\emptyset$ is the left derivative.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. 22, Proposition 3; (29), (K1), (30)

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC1_Thresholds

namespace SuspensionContract.HighCostC1
theorem proposition_3 (P : Params) (hP : P.Standing) (h1 : P.Condition1)
    (hK : P.Kbar1 ≤ P.K ∧ P.K ≤ P.VbarFn P.what - P.vlow)
    (θ m : ℝ) (hθm : P.TangentPair P.K θ m) :
    P.OptCond (P.calV P.what) (P.V030 θ m) := by sorry
end SuspensionContract.HighCostC1
