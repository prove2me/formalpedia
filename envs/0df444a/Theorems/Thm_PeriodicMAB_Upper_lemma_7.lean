-- Prove2me | Theorems.Thm_PeriodicMAB_Upper_lemma_7
-- name    : PeriodicMAB.Upper.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:00.571504+00:00
-- url     : https://prove2.me/theorems/f5291ee7-7fc0-46c7-a51e-2049dcfdf617
-- title:
--   Lemma 7, p. 19 — maxima of the periodogram lie within $1/n$ of the present frequencies, w.p. $\ge1-200/n^{0.867H^2-1}-200/n^{0.6934H^2-1}$
-- statement:
--   Let the noise satisfy Assumption 2 with parameter $\sigma>0$, $H>0$, and let arm $k$ have a mean sequence of minimum period $T_k$ satisfying Assumption 3 (for this arm). If
--   $$
--   b_k\ge2\bar\epsilon_v+\frac{8\pi}{3}U_2B_k ,
--   $$
--   then, with probability at least $1-200/n^{0.867H^2-1}-200/n^{0.6934H^2-1}$, for every present frequency $j/T_k$ with $j\ge1$, every maximizer $v^*_j$ of $|\tilde y_k|$ over $[j/T_k-g/n,\ j/T_k+g/n]$ lies in $[j/T_k-1/n,\ j/T_k+1/n]$.
--
--   Together with the separation of the candidate frequencies, this guarantees that Step 16 of Algorithm 1 snaps each selected maximum to the correct present frequency.
--
--   **Formalization Note** The paper prints the exponent $0.694H^2-1$. The proof applies Lemma 6 at $\delta=\tfrac34\bar\epsilon_v$, and the first exponent becomes $0.23280625\cdot\tfrac{9}{16}\cdot\tfrac{4}{(1-\pi/24)^2}\approx0.69349$, not $0.694$; the statement uses $0.6934$. The exponent $0.867$ holds through the proof's unrounded second constant $0.291106$ (giving $0.86713$); from the rounded $0.291$ of Lemma 6 one gets only $0.86683$, so Lemma 7 does not follow from the stated Lemma 6 alone. The present frequency $j=0$ is excluded: its neighbourhood is not part of $\mathcal U_k$, so the proof does not cover it, and Theorem 2 does not use it. Stated as an upper bound on the probability of the bad event.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 19, Lemma 7

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace PeriodicMAB.Upper

/-- Lemma 7 (p. 19), with the exponent `0.6934` that the proof establishes in place of the
printed `0.694`, for the nonzero present frequencies: if `b_k ≥ 2ε̄_v + (8π/3)U₂B_k` then, with
probability at least `1 − 200/n^{0.867H²−1} − 200/n^{0.6934H²−1}`, every maximizer of `|ỹ_k|` on
`[j/p − g/n, j/p + g/n]` lies in `[j/p − 1/n, j/p + 1/n]`, for every present `j ≥ 1`. -/
theorem lemma_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (σ : ℝ≥0) (hσ : 0 < σ) (hε : IsSubGaussianNoise P ε σ)
    (μk : ℕ → ℝ) (p n g k : ℕ) (H : ℝ) (hH : 0 < H)
    (hper : IsMinPeriod μk p) (hA3 : Assumption3Arm n g p)
    (hb : 2 * epsBar σ H n + 8 * Real.pi / 3 * U2 n g * bigB μk p ≤ smallB μk p) :
    P {ω | ∃ j ∈ presentSet μk p, 1 ≤ j ∧
        ∃ v ∈ Set.Icc ((j : ℝ) / p - (g : ℝ) / n) ((j : ℝ) / p + (g : ℝ) / n),
          (∀ w ∈ Set.Icc ((j : ℝ) / p - (g : ℝ) / n) ((j : ℝ) / p + (g : ℝ) / n),
            ‖yTilde μk ε n k w ω‖ ≤ ‖yTilde μk ε n k v ω‖) ∧
          1 / (n : ℝ) < |v - (j : ℝ) / p|} ≤
      ENNReal.ofReal (200 / (n : ℝ) ^ (0.867 * H ^ 2 - 1) + 200 / (n : ℝ) ^ (0.6934 * H ^ 2 - 1)) := by sorry

end PeriodicMAB.Upper
