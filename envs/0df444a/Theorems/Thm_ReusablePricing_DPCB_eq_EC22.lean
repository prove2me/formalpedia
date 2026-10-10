-- Prove2me | Theorems.Thm_ReusablePricing_DPCB_eq_EC22
-- name    : ReusablePricing.DPCB.eq_EC22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:54.266993+00:00
-- url     : https://prove2.me/theorems/9836d0c9-1866-46dc-a121-d7e597cf4a7a
-- title:
--   (EC.22), ec11 — on 𝒢(ϵ, m, δ), DPC-B posts λᵗ_k = λ^{t,D}_k − (ϵ_k/n̲_k + Σ_{𝒯_k^{β_k(t)−1}} Δ^s_k/m_k)·1{λ^{t,D}_k > 0}
-- statement:
--   Under the hypotheses of Lemma EC.3 (standing hypotheses of Section 6, a valid batch partition, $1 \le m_k \le \underline{n}_k$, the upper bound on $\epsilon_k$, and $\delta^b_k$ as in (EC.17)), on every sample path of positive probability in $\mathcal{G}(\epsilon, m, \delta)$, the rates posted by DPC-B$(m,\epsilon)$ are, for all $t \in [1,T]$ and all types $k$,
--   $$
--   \lambda^t_k = \lambda^{t,D}_k - \Bigl(\frac{\epsilon_k}{\underline{n}_k} + \frac{1}{m_k}\sum_{s \in \mathcal{T}_k^{\beta_k(t)-1}} \Delta^s_k\Bigr) \mathbf{1}\{\lambda^{t,D}_k > 0\}.
--   $$
--
--   So on the good event no type is turned off and no projection is active. This identity feeds the Taylor expansion of Step 2 of the proof of Theorem 3.
--
--   **Formalization Note** The page introduces (EC.22) as "a consequence of Lemma EC.1" on "$\mathcal{G}(\epsilon,\delta)$"; in Section EC.4 these read Lemma EC.3 and $\mathcal{G}(\epsilon, m, \delta)$. DPC-B admits type $k$ when $\tilde C(t, t+\ell_k) \succeq A^k$, whereas Lemma EC.3 controls $C^t = \tilde C(t,t)$; the page does not spell out this step when $\ell_k > 0$. The statement is posed as printed.
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), p. ec11, (EC.22)

import Mathlib
import Definitions.Def_ReusablePricing_DPCB_Events

open Finset

namespace ReusablePricing.DPCB

open General

/-- Display (EC.22) (ec11): under the hypotheses of Lemma EC.3, on every path of positive
probability in `𝒢(ϵ, m, δ)`, DPC-B(m, ϵ) posts, for all `t ∈ [1, T]` and all `k`,
`λ^t_k = λ^{t,D}_k - (ϵ_k/n̲_k + (1/m_k) ∑_{s ∈ 𝒯_k^{β_k(t)-1}} Δ^s_k) 1{λ^{t,D}_k > 0}`. -/
theorem eq_EC22 (P : General) (R Ψ φL φU : ℝ) (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ)
    (β : Fin P.K → ℕ → ℕ) (B : Fin P.K → ℕ)
    (hst : P.Standing R Ψ φL φU nl) (hbat : P.BatchesValid m β B)
    (hm : ∀ k, 1 ≤ m k ∧ m k ≤ nl k)
    (hε : ∀ k, ε k ≤ (nl k : ℝ) *
      min 1 ((1 + 4 * (m k : ℝ) * min φL φU) / ((nl k : ℝ) + 4 * (m k : ℝ))))
    (ω : P.Path) (hω : 0 < P.pathProb nl m ε β ω)
    (hG : P.inG nl m ε β B (P.delta nl ε β) ω) :
    ∀ t ∈ Icc 1 P.T, ∀ k,
      P.rate nl m ε β t ω k =
        P.lamD t k - (ε k / (nl k : ℝ) + 1 / (m k : ℝ) * P.prevErr nl m ε β t ω k) *
          (if 0 < P.lamD t k then 1 else 0) := by sorry

end ReusablePricing.DPCB
