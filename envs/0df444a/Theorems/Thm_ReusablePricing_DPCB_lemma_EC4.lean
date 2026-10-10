-- Prove2me | Theorems.Thm_ReusablePricing_DPCB_lemma_EC4
-- name    : ReusablePricing.DPCB.lemma_EC4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:10:03.687969+00:00
-- url     : https://prove2.me/theorems/b760e4eb-7357-4a0c-8272-3d80b6c528e9
-- title:
--   Lemma EC.4 as proved in (EC.23), ec12 — P(𝒢̄(ϵ, m, δ)) ≤ Σ_k (4T/m_k) exp{min{maxᵢCᵢ, m_k}γ_k² − (min_k ϵ_k − 1)γ_k/(8K)}
-- statement:
--   Consider the general setting of Section 6 under its standing hypotheses, a valid batch partition with $1 \le m_k \le \underline{n}_k$, and buffers in the range of Theorem 3,
--   $$
--   1 < \epsilon_k \le \min\Bigl\{ \underline{n}_k \min\Bigl\{1, \frac{1 + 4 m_k \min\{\varphi_L,\varphi_U\}}{4m_k + \underline{n}_k}\Bigr\},\ 1 + 16 \min\{\max_i C_i, m_k\} \Bigr\}.
--   $$
--   Let $\delta^b_k$ be chosen as in (EC.17). Then for all $\gamma_1, \dots, \gamma_K \in (0,1]$, the probability under DPC-B$(m,\epsilon)$ that the good event fails satisfies
--   $$
--   \mathbf{P}\bigl(\bar{\mathcal{G}}(\epsilon, m, \delta)\bigr) \le \sum_{k=1}^K \frac{4T}{m_k} \exp\Bigl\{ \min\{\max_i C_i, m_k\}\, \gamma_k^2 - \frac{\min_j \epsilon_j - 1}{8K}\, \gamma_k \Bigr\}.
--   $$
--
--   This is the concentration step of the proof of Theorem 3: with $\gamma_k$ of order $(\min_j\epsilon_j - 1)/(K \min\{\max_i C_i, m_k\})$ it yields the exponential term of display (8).
--
--   **Formalization Note** The printed Lemma EC.4 has $(\min_k \epsilon_k - 1)/(4K)$ in the exponent. Its proof ends at (EC.23) with $8K$, using $(\underline{n}-1)/\underline{n} \ge 1/2$, and Step 2 uses the $8K$ form; the statement here is the one the proof establishes. The printed lemma lists no range for $\epsilon$; the range of Theorem 3 is assumed, as in the proof of Theorem 3 where the lemma is used.
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), p. ec12, Lemma EC.4 and (EC.23)

import Mathlib
import Definitions.Def_ReusablePricing_DPCB_Events

open Finset

namespace ReusablePricing.DPCB

open General

/-- Lemma EC.4 as proved in (EC.23) (ec12): with `δ^b_k` as in (EC.17), for all
`γ_k ∈ (0, 1]`,
`P(𝒢̄(ϵ, m, δ)) ≤ ∑_k (4T/m_k) exp{min{max_i C_i, m_k} γ_k² - ((min_j ϵ_j - 1)/(8K)) γ_k}`. -/
theorem lemma_EC4 (P : General) (R Ψ φL φU : ℝ) (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ)
    (β : Fin P.K → ℕ → ℕ) (B : Fin P.K → ℕ)
    (hst : P.Standing R Ψ φL φU nl) (hbat : P.BatchesValid m β B)
    (hm : ∀ k, 1 ≤ m k ∧ m k ≤ nl k)
    (hε : ∀ k, 1 < ε k ∧
      ε k ≤ min ((nl k : ℝ) * min 1 ((1 + 4 * (m k : ℝ) * min φL φU) / (4 * (m k : ℝ) + (nl k : ℝ))))
                (1 + 16 * min P.maxC (m k : ℝ))) :
    ∀ γ : Fin P.K → ℝ, (∀ k, 0 < γ k ∧ γ k ≤ 1) →
      P.prob nl m ε β (fun ω => ¬ P.inG nl m ε β B (P.delta nl ε β) ω) ≤
        ∑ k, 4 * (P.T : ℝ) / (m k : ℝ) *
          Real.exp (min P.maxC (m k : ℝ) * γ k ^ 2 - (P.epsMin ε - 1) / (8 * (P.K : ℝ)) * γ k) := by sorry

end ReusablePricing.DPCB
