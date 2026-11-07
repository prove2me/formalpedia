-- Prove2me | Theorems.Thm_PrivRobustStat_lemma_9
-- name    : PrivRobustStat.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:23.655402+00:00
-- url     : https://prove2.me/theorems/c9bd1d5e-9630-4533-8da1-84a4a07bb9fa
-- title:
--   Lemma 9, p.22 — PrivateSoftFilter (loop and binary search) gives (22) with probability $1-\beta$
-- statement:
--   **Lemma 9** (utility of PrivateSoftFilter). Let $\bar w\in[0,\tfrac1n]^n$, $\tau\in[0,\tau_{\max}]^n$, $\kappa,\tau_{\max}>0$, $\beta\in(0,\tfrac14)$, $G\subseteq[n]$ and $B=[n]\setminus G$. If $\sum_{i\in G}\bar w_i\tau_i\le\kappa/60$ and $\tau_{\max}\ge2\kappa$, then with probability at least $1-\beta$ Algorithm 4 returns $w'$ with $0_n\le w'\le\bar w$ and
--
--   $$\sum_{i\in[n]}w'_i\tau_i\le\frac{9\kappa}{20},\qquad\|[\bar w-w']_G\|_1\le\tfrac12\|[\bar w-w']_B\|_1.\tag{22}$$
--
--   This holds both for the loop as printed and for the binary-search implementation of the proof, which Algorithm 1 uses.
--
--   Differences from the source:
--   - encoding: Algorithm 4 and "an implementation of Algorithm 4" → (22) stated for both the printed loop and the binary search of the proof; reason: the lemma's proof covers both, and Algorithm 1 and Lemma 10 use the binary search
--   - encoding: a fresh draw ξ_t for each query → the draw with index t for the query of F(t); reason: each form queries every t at most once, so each query has fresh noise
--   - encoding: with probability at least 1 − β → a measurable event of the Gaussian draws with that probability; reason: avoids outer measure; same claim
--   - encoding: "running in time O(n log(τ_max/κ))" → not in this item; the mission goal theorem_4 bounds the work of a machine program; reason: the item states the algorithm as a random map of data and noise, which has no cost (planning decision 10)
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Lemma 9, p.22 (PDF p.25); binary search in its proof, p.23

import Mathlib
import Definitions.Def_PrivRobustStat_Privacy
import Definitions.Def_PrivRobustStat_Filter

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-- **Lemma 9** (utility of `PrivateSoftFilter`), p.22 (PDF p.25); the binary-search implementation in
its proof, p.23.

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"Suppose that the inputs to Algorithm 4 satisfy ∑_{i∈G} w̄_iτ_i ≤ κ/60 and τ_max ≥ 2κ. With
probability ≥ 1 − β, Algorithm 4 returns w′ such that 0_n ≤ w′ ≤ w̄, and ∑_{i∈[n]} w′_iτ_i ≤ 9κ/20,
∥[w̄ − w′]_G∥₁ ≤ ½∥[w̄ − w′]_B∥₁. (22) Furthermore, there is an implementation of Algorithm 4 running
in time O(n log(τ_max/κ))."

**Formalization Note.** Algorithm 4's inputs: `w̄ ∈ [0, 1/n]^n`, `τ ∈ [0, τ_max]^n`, `κ, τ_max > 0`,
`β ∈ (0, 1/4)`; `G ⊆ [n]` any set and `B := [n] \ G`. (22) is stated for both forms: the loop as
printed (`softFilterLoop`) and the binary-search implementation (`softFilterBin`), each on a
measurable event of probability `≥ 1 − β` of the draws `ξ` (`stdGauss ℕ`, `ξ_t` for the query of
`F(t)`). The running time is carried by the goal theorem's time clause. -/
theorem lemma_9 {n : ℕ} (wbar τ : Fin n → ℝ) (κ τmax β : ℝ) (G : Finset (Fin n))
    (hw : InBox n wbar) (hτ : ∀ i, 0 ≤ τ i ∧ τ i ≤ τmax) (hκ : 0 < κ) (hτmax : 0 < τmax)
    (hβ : 0 < β) (hβ' : β < 1 / 4) (hG : ∑ i ∈ G, wbar i * τ i ≤ κ / 60) (h2 : 2 * κ ≤ τmax) :
    (∃ E : Set (ℕ → ℝ), MeasurableSet E ∧ ENNReal.ofReal (1 - β) ≤ stdGauss ℕ E ∧
      ∀ ξ ∈ E,
        (∀ i, 0 ≤ softFilterLoop wbar τ κ τmax β ξ i ∧ softFilterLoop wbar τ κ τmax β ξ i ≤ wbar i) ∧
        ∑ i, softFilterLoop wbar τ κ τmax β ξ i * τ i ≤ 9 * κ / 20 ∧
        l1 (restrict (wbar - softFilterLoop wbar τ κ τmax β ξ) G) ≤
          1 / 2 * l1 (restrict (wbar - softFilterLoop wbar τ κ τmax β ξ) Gᶜ)) ∧
    (∃ E : Set (ℕ → ℝ), MeasurableSet E ∧ ENNReal.ofReal (1 - β) ≤ stdGauss ℕ E ∧
      ∀ ξ ∈ E,
        (∀ i, 0 ≤ softFilterBin wbar τ κ τmax β ξ i ∧ softFilterBin wbar τ κ τmax β ξ i ≤ wbar i) ∧
        ∑ i, softFilterBin wbar τ κ τmax β ξ i * τ i ≤ 9 * κ / 20 ∧
        l1 (restrict (wbar - softFilterBin wbar τ κ τmax β ξ) G) ≤
          1 / 2 * l1 (restrict (wbar - softFilterBin wbar τ κ τmax β ξ) Gᶜ)) := by sorry

end PrivRobustStat
