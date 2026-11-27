-- Prove2me | Theorems.Thm_SPPRevenue_SingleUnit_Supplement_lemma_3
-- name    : SPPRevenue.SingleUnit.Supplement.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:14:33.472703+00:00
-- url     : https://prove2.me/theorems/24928053-eeec-4444-8047-e2353295937a
-- title:
--   Lemma 3 — Myersonian SPP_H sells at least H − Σ_{i<H}(H−i)C(n,i)(s⋆/n)^i(1−s⋆/n)^{n−i} units at price ≥ τ
-- statement:
--   Consider $H\ge1$ units, $n\ge1$ buyers with independent values $v_i\sim\mu_i$, and an $H$-unit threshold mechanism with thresholds $t_i(v_{-i})$. Let
--   $$s^\star(\tau)=\sum_{i=1}^n\mathbb P[v_i\ge t_i\ge\tau]$$
--   and let $m(\tau)$ be the expected number of units that the Myersonian SPP$_H$ mechanism (prices $t'_i$, re-sampled thresholds) sells at a price of at least $\tau$. Then for every $\tau\ge0$
--   $$m(\tau)\ \ge\ H-\sum_{i=0}^{H-1}(H-i)\binom ni\frac{s^\star(\tau)^i}{n^i}\Big(1-\frac{s^\star(\tau)}n\Big)^{n-i}.$$
--
--   The right-hand side is $H$ minus the expected unused capacity under a binomial number of acceptances; the lemma gives the second constraint of the program (FR-Multi(H)) in Theorem 3.
--
--   **Formalization Note** $m(\tau)$ is computed from the served set of SPP$_H$ under the re-sampled prices; $s^\star(\tau)\le n$ is finite, so its real value is used. For $i>n$ the binomial coefficient is $0$, so the natural-number exponent $n-i$ does not matter.
--
--   Differences from the source:
--   - generalization: t are the thresholds of the optimal H-unit mechanism, for atomless or finitely supported value laws → t is any H-unit threshold mechanism (measurable, nonnegative, own-value independent, almost surely at most H buyers above their thresholds), for arbitrary value laws; reason: the proof uses only these properties; the optimal mechanism's thresholds satisfy them
--   - encoding: τ a price level → τ ≥ 0; reason: prices and thresholds are nonnegative; for τ < 0 both sides equal their value at τ = 0
--   - encoding: an n-buyer setting, [n] = {1, …, n} → 1 ≤ n, buyers Fin n (index i is buyer i + 1); reason: n ≥ 1 is the setting's standing range; q_n and r_n are undefined at n = 0
--   - encoding: m(τ), expected number of units sold at price ≥ τ → lower integral of the number of served buyers with re-sampled price ≥ τ; reason: Lean convention for the expectation of a count
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, p. 19, Lemma 3; proof §8.4, pp. 35–38

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_MultiUnit

namespace SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

theorem lemma_3 (H : ℕ) (hH : 1 ≤ H) {n : ℕ} (hn : 1 ≤ n) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (t : Fin n → (Fin n → ℝ) → ℝ)
    (ht : IsMultiThresholdMech H μ t) (τ : ℝ) (hτ : 0 ≤ τ) :
    ENNReal.ofReal ((H : ℝ) - ∑ i ∈ Finset.range H,
        ((H : ℝ) - i) * (n.choose i : ℝ) * ((sStar μ t τ).toReal ^ i / (n : ℝ) ^ i) *
          (1 - (sStar μ t τ).toReal / n) ^ (n - i)) ≤ mH H μ t τ := by sorry

end SPPRevenue.SingleUnit.Supplement
