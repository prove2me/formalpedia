-- Prove2me | Theorems.Thm_QuantumMC_MeanEst_lemma_4_band_bound
-- name    : QuantumMC.MeanEst.lemma_4_band_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:47.817096+00:00
-- url     : https://prove2.me/theorems/e8b0eade-ec6e-43c0-9d37-4726f0356d7e
-- title:
--   §2.2, proof of Lemma 4 — band second-moment bound
-- statement:
--   Let $X$ be nonnegative with a finite second moment and $\ell\ge1$. On the band $[2^{\ell-1},2^\ell)$,
--
--   $$\mathbb E[X_{[2^{\ell-1},2^\ell)}]\le\frac{\|X_{[2^{\ell-1},2^\ell)}\|_2^2}{2^{\ell-1}}.$$
--
--   This bounds each band mean by its second moment.
-- source:
--   Montanaro, Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, §2.2, proof of Lemma 4, p. 11

import Mathlib
import Definitions.Def_QuantumMC_MeanEst_Setting

namespace QuantumMC.MeanEst

open MeasureTheory ProbabilityTheory

/-- §2.2, proof of Lemma 4, p. 11: one dyadic band's first moment is bounded by its second. -/
theorem lemma_4_band_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P)
    (hpos : ∀ ω, 0 ≤ X ω) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∫ ω, truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω ∂P) ≤
      l2norm P (truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X) ^ 2 /
        (2 : ℝ) ^ (ℓ - 1) := by sorry
end QuantumMC.MeanEst
