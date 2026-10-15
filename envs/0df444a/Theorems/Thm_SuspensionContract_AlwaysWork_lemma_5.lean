-- Prove2me | Theorems.Thm_SuspensionContract_AlwaysWork_lemma_5
-- name    : SuspensionContract.AlwaysWork.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:30.915143+00:00
-- url     : https://prove2.me/theorems/b96c3ae3-8956-49a7-8ef6-98200564aa14
-- title:
--   Lemma 5, p. 24 — under Condition 2 and K ∈ [K̲, K̄₂) there are (c_K, m_K, θ̲_K) solving (35)–(38), monotone in K
-- statement:
--   Assume the standing assumptions and Condition 2. For every switching cost $K>0$ with $K\in[\underline K,\bar K_2)$ there are parameters $(c_K,m_K,\underline\theta_K)$, with $\underline\theta_K\in(0,\bar w)$, such that
--   $$c_K>0,\qquad m_K\in\Big[\frac{\rho-r}{\rho-r-\mu},\ \frac{\bar V-\underline v}{\bar w}\Big)\quad(35),$$
--   $$V_{c_K}(\underline\theta_K)=\bar V+m_K(\underline\theta_K-\bar w)\ (36),\qquad V_{c_K}'(\underline\theta_K)=m_K\ (37),\qquad V_{c_K}(\bar w)=\bar V-K\ (38),$$
--   where $V_c(w)=\underline v+w+c\,w^{r/\rho}$. Moreover, as functions of $K$ on this range, $c_K$ is strictly decreasing, $m_K$ strictly increasing and $\underline\theta_K$ strictly decreasing.
--
--   This lemma supplies the parameters from which the value functions (39)–(40) of Proposition 5 are built; it is what makes Proposition 5 a statement about existing objects.
--
--   **Formalization Note.** The switching cost is a bound variable $K$ ranging over $\{K>0:\underline K\le K<\bar K_2\}$; $K>0$ is the model's standing assumption (with $\underline K=0$ when $R>\bar R$, the interval would otherwise contain $0$). The field `P.K` is not used, since none of $\underline K,\bar K_2,\bar V,\bar w,V_c$ depends on it. The paper prints (36) as $V_{c_K}(\underline\theta_K)=\bar V+m_K(w-\bar w)$ with a free $w$; the proof (EC.67) and the definition (40) show it should be $\underline\theta_K$. The range $\underline\theta_K\in(0,\bar w)$ is not in the lemma's statement but is given by its proof (Lemma EC.3) and is needed for (40). $\underline K$ is (33) with the misprint corrected (see the Setting). "Decreasing/increasing" are strict.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. 24, Lemma 5, (35)–(38)

import Mathlib
import Definitions.Def_SuspensionContract_AlwaysWork_Setting

namespace SuspensionContract.AlwaysWork

/-- Lemma 5, p. 24: under Condition 2, for every switching cost `K` with `K > 0` and
`K ∈ [K̲, K̄₂)` there are parameters `(c_K, m_K, θ̲_K)` with `θ̲_K ∈ (0, w̄)`, `c_K > 0`,
`m_K ∈ [(ρ − r)/(ρ − r − µ), (V̄ − v̲)/w̄)` (35), satisfying (36) (with `θ̲_K` in place of the
printed free `w`), (37) and (38); moreover `c_K` is strictly decreasing, `m_K` strictly increasing
and `θ̲_K` strictly decreasing in `K`. The switching cost is the bound variable `K`; the field
`P.K` is not used (none of `K̲`, `K̄₂`, `V̄`, `w̄`, `V_c` depends on it). -/
theorem lemma_5 (P : Params) (hP : P.Standing) (h2 : P.Condition2) :
    ∃ cK mK θK : ℝ → ℝ,
      (∀ K : ℝ, 0 < K → P.Klow ≤ K → K < P.Kbar2 →
        (0 < θK K ∧ θK K < P.wbar) ∧ 0 < cK K ∧
        ((P.ρ - P.r) / (P.ρ - P.r - P.μ) ≤ mK K ∧ mK K < (P.Vbar - P.vlow) / P.wbar) ∧
        P.Vc (cK K) (θK K) = P.Vbar + mK K * (θK K - P.wbar) ∧
        deriv (P.Vc (cK K)) (θK K) = mK K ∧
        P.Vc (cK K) P.wbar = P.Vbar - K) ∧
      StrictAntiOn cK {K : ℝ | 0 < K ∧ P.Klow ≤ K ∧ K < P.Kbar2} ∧
      StrictMonoOn mK {K : ℝ | 0 < K ∧ P.Klow ≤ K ∧ K < P.Kbar2} ∧
      StrictAntiOn θK {K : ℝ | 0 < K ∧ P.Klow ≤ K ∧ K < P.Kbar2} := by sorry

end SuspensionContract.AlwaysWork
