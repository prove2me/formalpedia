-- Prove2me | Theorems.Thm_QuantumMC_MeanEst_lemma_4_decomposition
-- name    : QuantumMC.MeanEst.lemma_4_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:44.006889+00:00
-- url     : https://prove2.me/theorems/28bb690f-5ce7-4396-b616-80956962545e
-- title:
--   §2.2, proof of Lemma 4 — dyadic decomposition
-- statement:
--   For an integrable nonnegative output $X$ and a natural number $k$, the mean splits into the base interval, $k$ half-open dyadic bands, and the upper tail:
--
--   $$\mathbb E[X]=\mathbb E[X_{[0,1)}]+\sum_{\ell=1}^{k}2^\ell\mathbb E[X_{[2^{\ell-1},2^\ell)}/2^\ell]+\mathbb E[X_{[2^k,\infty)}].$$
--
--   This identity fixes the band boundaries and the scaling used by Algorithm 2.
-- source:
--   Montanaro, Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, §2.2, proof of Lemma 4, p. 10

import Mathlib
import Definitions.Def_QuantumMC_MeanEst_Setting

namespace QuantumMC.MeanEst

open MeasureTheory ProbabilityTheory

/-- §2.2, proof of Lemma 4, p. 10: the dyadic decomposition of the mean. -/
theorem lemma_4_decomposition {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P)
    (hpos : ∀ ω, 0 ≤ X ω) (k : ℕ) :
    (∫ ω, X ω ∂P) = (∫ ω, truncIco 0 1 X ω ∂P) +
      (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * (∫ ω, band X ℓ ω ∂P)) +
      (∫ ω, truncGe ((2 : ℝ) ^ k) X ω ∂P) := by sorry
end QuantumMC.MeanEst
