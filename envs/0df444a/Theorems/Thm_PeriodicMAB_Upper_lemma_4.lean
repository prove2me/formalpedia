-- Prove2me | Theorems.Thm_PeriodicMAB_Upper_lemma_4
-- name    : PeriodicMAB.Upper.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:47.254402+00:00
-- url     : https://prove2.me/theorems/573e5457-4ad3-41c9-b90e-73a36c7a4649
-- title:
--   Lemma 4, p. 19 — $\sup_{v\in\bar{\mathcal V}_k}|\tilde y_k(v)|\le\tau_k$ with probability at least $1-48/n^{H^2-1}$
-- statement:
--   Let the noise satisfy Assumption 2 with parameter $\sigma>0$, let $H>0$, and let arm $k$ have a mean sequence of minimum period $T_k$ satisfying Assumption 3 (for this arm). Then
--   $$
--   \mathbb P\Big(\sup_{v\in\bar{\mathcal V}_k}|\tilde y_k(v)|\le\tau_k\Big)\ge1-\frac{48}{n^{H^2-1}} .
--   $$
--
--   Off the neighbourhoods of the present frequencies the periodogram stays below the threshold, so Algorithm 1 selects no spurious frequency there.
--
--   **Formalization Note** Stated as $\mathbb P(\exists v\in\bar{\mathcal V}_k:\ |\tilde y_k(v)|>\tau_k)\le 48/n^{H^2-1}$ (outer measure), with $n^{H^2-1}$ a real power.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 19, Lemma 4

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace PeriodicMAB.Upper

/-- Lemma 4 (p. 19): `sup_{v ∈ 𝒱̄_k} |ỹ_k(v)| ≤ τ_k` with probability at least `1 − 48/n^{H²−1}`. -/
theorem lemma_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (σ : ℝ≥0) (hσ : 0 < σ) (hε : IsSubGaussianNoise P ε σ)
    (μk : ℕ → ℝ) (p n g k : ℕ) (H : ℝ) (hH : 0 < H)
    (hper : IsMinPeriod μk p) (hA3 : Assumption3Arm n g p) :
    P {ω | ∃ v ∈ nbhdVbar μk p n g, tau μk ε σ H n g k ω < ‖yTilde μk ε n k v ω‖} ≤
      ENNReal.ofReal (48 / (n : ℝ) ^ (H ^ 2 - 1)) := by sorry

end PeriodicMAB.Upper
