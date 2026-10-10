-- Prove2me | Theorems.Thm_ReusablePricing_DPCB_lemma_EC3
-- name    : ReusablePricing.DPCB.lemma_EC3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:54.95237+00:00
-- url     : https://prove2.me/theorems/2135b1e3-fff1-4313-9f3b-c84f2cd48a1d
-- title:
--   Lemma EC.3, ec9 — on 𝒢(ϵ, m, δ): Cᵗ ⪰ e and λ^{t,D}_k − ϵ_k/n̲_k − (Σ_{𝒯_k^{β_k(t)−1}} Δ^s_k)/m_k ∈ (0, λ_U)
-- statement:
--   Consider the general setting of Section 6 under its standing hypotheses, a valid batch partition with $1 \le m_k \le \underline{n}_k$ for every type $k$, and buffers satisfying
--   $$
--   \epsilon_k \le \underline{n}_k \min\Bigl\{1, \frac{1 + 4 m_k \min\{\varphi_L, \varphi_U\}}{\underline{n}_k + 4 m_k}\Bigr\} \quad \text{for all } k .
--   $$
--   Let $\delta^b_k$ be chosen as in (EC.17). Then, on every sample path of positive probability under DPC-B$(m,\epsilon)$ that lies in $\mathcal{G}(\epsilon, m, \delta)$, the following hold for all $t \in [1,T]$:
--   1. $C^t \succeq e$, that is, at least one unit of every resource is free at the beginning of period $t$;
--   2. for every $k$, if $\lambda^{t,D}_k \in (0,\lambda_U)$ then
--   $$
--   \lambda^{t,D}_k - \frac{\epsilon_k}{\underline{n}_k} - \frac{1}{m_k}\sum_{s \in \mathcal{T}_k^{\beta_k(t)-1}} \Delta^s_k \in (0, \lambda_U).
--   $$
--
--   On the good event the control therefore never runs out of capacity and its projected rates are never clipped; this is the first step of the proof of Theorem 3.
--
--   **Formalization Note** $C^t$ is not defined in Section 6; it is taken as $\tilde C(t,t)$, the units free at period $t$ after all requests of periods before $t$ (p. 18's definition of $\tilde C$ and p. 11's "available resources at the beginning of period $t$"). The proof of Lemma EC.3 writes $C^t_i = C_i - \sum_k \sum_{s=(t-n_k-\ell_k+1)^+}^{(t-\ell_k-1)^+} a_{ik} D^s_k$, which leaves out requests whose service starts exactly at period $t$; for $\ell \equiv 0$ the two agree. "On $\mathcal{G}$" is read on paths of positive probability, where a turned-off type has no arrival. $m_k \ge 1$ is the "sequence of positive integers" of p. 18. The standing hypotheses include A4 and A5, which this lemma does not need beyond the $\varphi_L, \varphi_U$ part of A5.
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), p. ec9, Lemma EC.3 and (EC.17)

import Mathlib
import Definitions.Def_ReusablePricing_DPCB_Events

open Finset

namespace ReusablePricing.DPCB

open General

/-- Lemma EC.3 (ec9): with `ϵ_k ≤ n̲_k min{1, (1 + 4 m_k min{φL, φU})/(n̲_k + 4 m_k)}`,
`m_k ≤ n̲_k` and `δ^b_k` as in (EC.17), on every path of positive probability in `𝒢(ϵ, m, δ)`,
for all `t ∈ [1, T]`: (i) `C^t ⪰ e`; and (ii) for all `k`, `λ^{t,D}_k ∈ (0, λ_U)` implies
`λ^{t,D}_k - ϵ_k/n̲_k - (∑_{s ∈ 𝒯_k^{β_k(t)-1}} Δ^s_k)/m_k ∈ (0, λ_U)`. -/
theorem lemma_EC3 (P : General) (R Ψ φL φU : ℝ) (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ)
    (β : Fin P.K → ℕ → ℕ) (B : Fin P.K → ℕ)
    (hst : P.Standing R Ψ φL φU nl) (hbat : P.BatchesValid m β B)
    (hm : ∀ k, 1 ≤ m k ∧ m k ≤ nl k)
    (hε : ∀ k, ε k ≤ (nl k : ℝ) *
      min 1 ((1 + 4 * (m k : ℝ) * min φL φU) / ((nl k : ℝ) + 4 * (m k : ℝ))))
    (ω : P.Path) (hω : 0 < P.pathProb nl m ε β ω)
    (hG : P.inG nl m ε β B (P.delta nl ε β) ω) :
    ∀ t ∈ Icc 1 P.T,
      (∀ i, 1 ≤ P.Ccur t ω i) ∧
      ∀ k, 0 < P.lamD t k → P.lamD t k < P.lamU →
        0 < P.lamD t k - ε k / (nl k : ℝ) - P.prevErr nl m ε β t ω k / (m k : ℝ) ∧
        P.lamD t k - ε k / (nl k : ℝ) - P.prevErr nl m ε β t ω k / (m k : ℝ) < P.lamU := by sorry

end ReusablePricing.DPCB
