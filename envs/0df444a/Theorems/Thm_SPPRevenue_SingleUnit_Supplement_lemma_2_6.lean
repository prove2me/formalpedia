-- Prove2me | Theorems.Thm_SPPRevenue_SingleUnit_Supplement_lemma_2_6
-- name    : SPPRevenue.SingleUnit.Supplement.lemma_2_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:20:08.042147+00:00
-- url     : https://prove2.me/theorems/5d2e760c-2c6b-4497-a62f-904664ab24e4
-- title:
--   Lemma 2 (6) — 2P[Z_τ = 0] + P[Z_τ = 1] ≤ r_n(s⋆(τ)) ≤ (2 + s⋆(τ))e^{−s⋆(τ)}, with r_n → (2 + y)e^{−y}
-- statement:
--   Consider a single item, $n\ge1$ buyers with independent values $v_i\sim\mu_i$ and a single-unit threshold mechanism with thresholds $t_i(v_{-i})$. For each buyer draw an independent fresh profile and let $t'_i$ be the re-sampled threshold; let $Z_\tau=\sum_{i=1}^n\mathbb I(v_i\ge t'_i\ge\tau)$ and $s^\star(\tau)=\sum_i\mathbb P[v_i\ge t_i\ge\tau]$. With $r_n(y)=2(1-y/n)^n+y(1-y/n)^{n-1}$, for every $\tau\ge0$
--   $$2\,\mathbb P[Z_\tau=0]+\mathbb P[Z_\tau=1]\ \le\ r_n(s^\star(\tau))\ \le\ (2+s^\star(\tau))\,e^{-s^\star(\tau)},$$
--   and $r_N(s^\star(\tau))\to(2+s^\star(\tau))e^{-s^\star(\tau)}$ as $N\to\infty$.
--
--   Inequality (6) bounds the probability that at most one buyer clears its re-sampled threshold; Theorems 5 and 6 use it for the Myersonian ESP auction. Inequality (5), the bound on $\mathbb P[Z_\tau=0]$ alone, is the published `SPPRevenue.SingleUnit.lemma_2`.
--
--   **Formalization Note** The pair (re-sampled profiles, values) has the law `resampleLaw` of the published setting and $Z_\tau$ is `ZTau`. The source's chain "$\le\lim_{n\to\infty}r_n(s^\star(\tau))=(2+s^\star(\tau))e^{-s^\star(\tau)}$" is split into the inequality with the limit value and the convergence statement.
--
--   Differences from the source:
--   - generalization: t are the thresholds of the optimal single-unit mechanism, for atomless or finitely supported value laws → any single-unit threshold mechanism (IsThresholdMech of the published setting), for arbitrary value laws; reason: the proof uses only the independence of the re-sampled thresholds; the optimal mechanism's thresholds are such a mechanism
--   - reading: r_n(s⋆(τ)) ≤ lim_{n→∞} r_n(s⋆(τ)) = (2 + s⋆(τ))e^{−s⋆(τ)} → r_n(s) ≤ (2 + s)e^{−s} together with r_N(s) → (2 + s)e^{−s}; reason: the chain states both facts
--   - encoding: Z_τ for a price level τ, n buyers → τ ≥ 0, 1 ≤ n; reason: the domain of the lemma; r_n is undefined at n = 0
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, p. 15, Lemma 2, inequality (6); proof §8.1, pp. 30–31

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Programs
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_EspProgram

namespace SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

theorem lemma_2_6 {n : ℕ} (hn : 1 ≤ n) (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (t : Fin n → (Fin n → ℝ) → ℝ) (ht : IsThresholdMech μ t) (τ : ℝ) (hτ : 0 ≤ τ) :
    2 * resampleLaw μ {x | ZTau t τ x = 0} + resampleLaw μ {x | ZTau t τ x = 1} ≤
        ENNReal.ofReal (rn n (sStar μ t τ).toReal) ∧
      rn n (sStar μ t τ).toReal ≤ rLim (sStar μ t τ).toReal ∧
      Filter.Tendsto (fun N : ℕ => rn N (sStar μ t τ).toReal) Filter.atTop
        (nhds (rLim (sStar μ t τ).toReal)) := by sorry

end SPPRevenue.SingleUnit.Supplement
