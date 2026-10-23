-- Prove2me | Theorems.Thm_SPPRevenue_SingleUnit_lemma_2
-- name    : SPPRevenue.SingleUnit.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:52.098506+00:00
-- url     : https://prove2.me/theorems/fecec336-7b0a-4a58-8ce1-dbf59e1ee15a
-- title:
--   Lemma 2 (5), p. 15 — P[Z_τ = 0] ≤ q_n(s⋆(τ)) ≤ e^{−s⋆(τ)}, with q_n(y) = (1 − y/n)^n → e^{−y}
-- statement:
--   Let $t$ be a single-unit threshold mechanism for $n$ buyers with independent values, let $t'_i$ be the Myersonian re-sampled thresholds, and let $Z_\tau = \sum_{i=1}^n \mathbf 1(v_i \ge t'_i \ge \tau)$. With $q_n(y) = (1 - y/n)^n$, for every $\tau$,
--   $$\mathbb P[Z_\tau = 0] \le q_n\big(s^\star(\tau)\big) \le e^{-s^\star(\tau)},$$
--   and $q_N(s^\star(\tau)) \to e^{-s^\star(\tau)}$ as $N \to \infty$.
--
--   Because the re-sampled thresholds are independent across buyers, the probability that no buyer clears a threshold of size at least $\tau$ is controlled by $s^\star(\tau)$ alone; this is the bound that turns the Myersonian revenue into the second constraint of the factor-revealing program.
--
--   **Formalization Note** The paper's chain "$\le \lim_{n\to\infty} q_n(s^\star(\tau)) = e^{-s^\star(\tau)}$" is stated as the inequality $q_n(s^\star(\tau)) \le e^{-s^\star(\tau)}$ together with the limit. $s^\star(\tau)$ is converted to a real number; it is finite (at most $1$) for a single-unit threshold mechanism. Inequality (6) of Lemma 2 is not included, as Theorem 1 does not use it.
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, p. 15, Lemma 2, Inequality (5)

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting

namespace SPPRevenue.SingleUnit

open MeasureTheory
open scoped ENNReal

theorem lemma_2 {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (t : Fin n → (Fin n → ℝ) → ℝ) (ht : IsThresholdMech μ t) (τ : ℝ) :
    resampleLaw μ {x | ZTau t τ x = 0} ≤ ENNReal.ofReal (qn n (sStar μ t τ).toReal) ∧
      qn n (sStar μ t τ).toReal ≤ Real.exp (-(sStar μ t τ).toReal) ∧
      Filter.Tendsto (fun N : ℕ => qn N (sStar μ t τ).toReal) Filter.atTop
        (nhds (Real.exp (-(sStar μ t τ).toReal))) := by sorry

end SPPRevenue.SingleUnit
