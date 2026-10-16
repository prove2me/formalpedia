-- Prove2me | Theorems.Thm_QuantumMC_MeanEst_lemma_4_cauchy_schwarz
-- name    : QuantumMC.MeanEst.lemma_4_cauchy_schwarz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:57.352474+00:00
-- url     : https://prove2.me/theorems/bb294927-9156-44b8-9df1-27b47b3dcc56
-- title:
--   §2.2, proof of Lemma 4 — dyadic Cauchy–Schwarz bound
-- statement:
--   For a nonnegative $L^2$ output $X$, write $X_\ell=X_{[2^{\ell-1},2^\ell)}$. For every natural $k$, both steps of the displayed bound hold:
--
--   $$\sum_{\ell=1}^k2^{\ell/2}\sqrt{\mathbb E[X_\ell]}\le\sqrt{k}\left(\sum_{\ell=1}^k2^\ell\mathbb E[X_\ell]\right)^{1/2}\le\sqrt{2k}\,\|X\|_2.$$
--
--   This is the sum bound used in Lemma 4. **Formalization Note** $2^{\ell/2}$ is written as $\sqrt{2^\ell}$.
-- source:
--   Montanaro, Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, §2.2, proof of Lemma 4, p. 11

import Mathlib
import Definitions.Def_QuantumMC_MeanEst_Setting

namespace QuantumMC.MeanEst

open MeasureTheory ProbabilityTheory

/-- §2.2, proof of Lemma 4, p. 11: both inequalities in the Cauchy–Schwarz display. -/
theorem lemma_4_cauchy_schwarz {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P)
    (hpos : ∀ ω, 0 ≤ X ω) (k : ℕ) :
    (∑ ℓ ∈ Finset.Icc 1 k,
        Real.sqrt ((2 : ℝ) ^ ℓ) *
          Real.sqrt (∫ ω, truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω ∂P)) ≤
      Real.sqrt (k : ℝ) *
        Real.sqrt (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ *
          (∫ ω, truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω ∂P)) ∧
    Real.sqrt (k : ℝ) *
        Real.sqrt (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ *
          (∫ ω, truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω ∂P)) ≤
      Real.sqrt (2 * (k : ℝ)) * l2norm P X := by sorry
end QuantumMC.MeanEst
