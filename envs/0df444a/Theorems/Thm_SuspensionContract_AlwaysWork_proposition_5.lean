-- Prove2me | Theorems.Thm_SuspensionContract_AlwaysWork_proposition_5
-- name    : SuspensionContract.AlwaysWork.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:20.498466+00:00
-- url     : https://prove2.me/theorems/05f2d365-5eae-423b-bbd3-3e5eb4cb9f9c
-- title:
--   Proposition 5, p. 25 — under Condition 2 and K ∈ [K̲, K̄₂) the smooth-pasted value functions (39)–(40) satisfy the optimality condition (20)–(22)
-- statement:
--   Assume the standing assumptions, Condition 2 ($\mu<\rho-r$ and $R\ge\hat R$) and $K\in[\underline K,\bar K_2)$. Let $(c_K,m_K,\underline\theta_K)$ be any parameters as in Lemma 5: $\underline\theta_K\in(0,\bar w)$, $c_K>0$, $m_K\in[\frac{\rho-r}{\rho-r-\mu},\frac{\bar V-\underline v}{\bar w})$, and
--   $$V_{c_K}(\underline\theta_K)=\bar V+m_K(\underline\theta_K-\bar w),\qquad V_{c_K}'(\underline\theta_K)=m_K,\qquad V_{c_K}(\bar w)=\bar V-K.$$
--   Then the functions $V_\emptyset$ of (39) and $V_I$ of (40) satisfy the optimality condition (20)–(22):
--   $$(\mathcal A_IV_I)(w)\ge0,\quad(\mathcal A_\emptyset V_\emptyset)(w)\ge0\quad(w>0),$$
--   $$0\le V_I(w)-V_\emptyset(w)\le K\quad(w\ge0),\qquad V_I(0)\ge\underline v,\quad V_\emptyset(0)\ge\underline v.$$
--
--   By the paper's verification theorem (Theorem 1), this certifies that in the medium-switching-cost regime the principal's optimal value is attained by a contract that never suspends the agent.
--
--   **Formalization Note.** The paper's companion claim (41), $U(\bar\Gamma)=\bar V-\bar w-K=V_\emptyset(\bar w)-\bar w$, concerns the utility of a contract and is not formalized. The theorem quantifies over every triple satisfying Lemma 5's conclusions; given $\underline\theta_K\in(0,\bar w)$ such a triple is unique (the equations (36)–(37) force $c_K=C^1(\underline\theta_K)$, $m_K=m(\underline\theta_K)$, and (38) has a unique root by Lemma EC.3), so this is the paper's claim. $\underline\theta_K\in(0,\bar w)$ comes from the proof of Lemma 5. Condition (20) is imposed for $w>0$: the right derivative of $V_{c_K}$ at $0$ is $+\infty$, so (20) at $w=0$ is an extended-real statement. Derivatives in $\mathcal A_I,\mathcal A_\emptyset$ are left derivatives, as on p. 15 of the paper. $\underline K$ uses the corrected (33).
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. 25, Proposition 5 (first claim), (39)–(40)

import Mathlib
import Definitions.Def_SuspensionContract_AlwaysWork_Setting
import Definitions.Def_SuspensionContract_AlwaysWork_ValueFunctions

namespace SuspensionContract.AlwaysWork

/-- Proposition 5 (first claim), p. 25: under Condition 2 and `K ∈ [K̲, K̄₂)`, for every triple
`(c_K, m_K, θ̲_K)` as in Lemma 5 (with `θ̲_K ∈ (0, w̄)`), the functions `V_∅` of (39) and `V_I`
of (40) satisfy the optimality condition (20)–(22) ((20) for `w > 0`). -/
theorem proposition_5 (P : Params) (hP : P.Standing) (h2 : P.Condition2)
    (hK : P.Klow ≤ P.K ∧ P.K < P.Kbar2) (cK mK θK : ℝ)
    (hθ : 0 < θK ∧ θK < P.wbar) (hc : 0 < cK)
    (hm : (P.ρ - P.r) / (P.ρ - P.r - P.μ) ≤ mK ∧ mK < (P.Vbar - P.vlow) / P.wbar)
    (h36 : P.Vc cK θK = P.Vbar + mK * (θK - P.wbar))
    (h37 : deriv (P.Vc cK) θK = mK)
    (h38 : P.Vc cK P.wbar = P.Vbar - P.K) :
    P.OptCond (P.VI40 cK mK θK) (P.V039 cK) := by sorry

end SuspensionContract.AlwaysWork
