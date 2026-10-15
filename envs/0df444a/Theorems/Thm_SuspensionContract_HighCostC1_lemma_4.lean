-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC1_lemma_4
-- name    : SuspensionContract.HighCostC1.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:50.717586+00:00
-- url     : https://prove2.me/theorems/d4fdae9a-f049-481e-a2b6-0c565eac7f2b
-- title:
--   Lemma 4, p. 22 — tangent pairs (θ̄^K, m^K) exist for K < V̄(ŵ) − v̲; θ̄^K increases, m^K decreases in K; θ̄^K → w̌(ŵ) as K ↓ 0
-- statement:
--   Assume the standing assumptions and Condition 1, and let $\hat{\mathrm w}$, $\mathcal V_{\hat{\mathrm w}}$, $\check w(\hat{\mathrm w})$ be as in Lemmas 2–3. Call $(\theta,m)$ a tangent pair for $K$ if $\theta\in[\check w(\hat{\mathrm w}),\hat{\mathrm w}]$, $m\in[0,\mathcal V_{\hat{\mathrm w}}'(0)]$ and
--
--   $$\mathcal V_{\hat{\mathrm w}}(\theta)=m\theta+K+\underline v,\qquad \mathcal V_{\hat{\mathrm w}}'(\theta)=m.\qquad(29)$$
--
--   Then:
--
--   1. for every $K\in(0,\bar V(\hat{\mathrm w})-\underline v)$ a tangent pair $(\bar\theta^K,m^K)$ exists;
--   2. for $0<K_1<K_2<\bar V(\hat{\mathrm w})-\underline v$ and tangent pairs $(\theta_1,m_1)$ for $K_1$ and $(\theta_2,m_2)$ for $K_2$, $\theta_1<\theta_2$ and $m_2<m_1$;
--   3. $\bar\theta^K\to\check w(\hat{\mathrm w})$ as $K\downarrow0$: for every $\varepsilon>0$ there is $\delta>0$ such that every tangent pair $(\theta,m)$ for any $K\in(0,\delta)$ with $K<\bar V(\hat{\mathrm w})-\underline v$ has $|\theta-\check w(\hat{\mathrm w})|<\varepsilon$.
--
--   The pair defines the suspension-state value function (30) and the switching-cost threshold $\bar K_1$ of (K1).
--
--   **Formalization Note** "Increasing/decreasing in $K$" are strict and are stated for any choice of tangent pairs, so they do not depend on a selection; likewise the limit is stated for every tangent pair. The paper's standing assumption $K>0$ is explicit because $K$ here is a free variable, not the model's switching cost.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. 22, Lemma 4 (29)

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC1_Thresholds

namespace SuspensionContract.HighCostC1
theorem lemma_4 (P : Params) (hP : P.Standing) (h1 : P.Condition1) :
    (∀ K, 0 < K → K < P.VbarFn P.what - P.vlow → ∃ θ m, P.TangentPair K θ m) ∧
      (∀ K₁ K₂ θ₁ m₁ θ₂ m₂, 0 < K₁ → K₁ < K₂ → K₂ < P.VbarFn P.what - P.vlow →
        P.TangentPair K₁ θ₁ m₁ → P.TangentPair K₂ θ₂ m₂ → θ₁ < θ₂ ∧ m₂ < m₁) ∧
      ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ K θ m, 0 < K → K < δ → K < P.VbarFn P.what - P.vlow →
        P.TangentPair K θ m → |θ - P.wcheck P.what| < ε := by sorry
end SuspensionContract.HighCostC1
