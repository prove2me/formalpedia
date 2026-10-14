-- Prove2me | Theorems.Thm_PeriodicMAB_Upper_lemma_5
-- name    : PeriodicMAB.Upper.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:43.48393+00:00
-- url     : https://prove2.me/theorems/6a96abe4-5e96-42e3-b207-9cf6ed4cfe47
-- title:
--   Lemma 5, p. 19 — under (13), $|\tilde y_k(j/T_k)|>\tau_k$ at every present frequency with probability at least $1-48/n^{H^2-1}$
-- statement:
--   Under the hypotheses of Lemma 4, assume in addition condition (13):
--   $$
--   b_k\ge\Big(\frac{2\pi U_1}{1-\pi U_2}+2\Big)\bar\epsilon_v+\Big(\frac{\pi U_1}{1-\pi U_2}\max\{\pi U_1,\pi U_2+1\}+\pi U_2\Big)B_k .
--   $$
--   Then, with probability at least $1-48/n^{H^2-1}$, $|\tilde y_k(j/T_k)|>\tau_k$ for every present frequency $j/T_k$, i.e. every $j\in\{0,\dots,T_k-1\}$ with $|b_{k,j}|>0$.
--
--   The threshold is therefore not so large that it hides a present frequency.
--
--   **Formalization Note** Stated as $\mathbb P(\exists j \text{ present}:\ |\tilde y_k(j/T_k)|\le\tau_k)\le48/n^{H^2-1}$. The present frequency $j=0$ is included, as in the paper's wording.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 19, Lemma 5, (13)

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace PeriodicMAB.Upper

/-- Lemma 5 (p. 19): under condition (13), `|ỹ_k(j/p)| > τ_k` at every present frequency
`j/p` with probability at least `1 − 48/n^{H²−1}`. -/
theorem lemma_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (σ : ℝ≥0) (hσ : 0 < σ) (hε : IsSubGaussianNoise P ε σ)
    (μk : ℕ → ℝ) (p n g k : ℕ) (H : ℝ) (hH : 0 < H)
    (hper : IsMinPeriod μk p) (hA3 : Assumption3Arm n g p)
    (h13 : (2 * Real.pi * U1 n g / (1 - Real.pi * U2 n g) + 2) * epsBar σ H n +
        (Real.pi * U1 n g / (1 - Real.pi * U2 n g) *
            max (Real.pi * U1 n g) (Real.pi * U2 n g + 1) + Real.pi * U2 n g) * bigB μk p ≤
        smallB μk p) :
    P {ω | ∃ j ∈ presentSet μk p, ‖yTilde μk ε n k ((j : ℝ) / p) ω‖ ≤ tau μk ε σ H n g k ω} ≤
      ENNReal.ofReal (48 / (n : ℝ) ^ (H ^ 2 - 1)) := by sorry

end PeriodicMAB.Upper
