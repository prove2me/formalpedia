-- Prove2me | Theorems.Thm_QuantumMC_MeanEst_theorem_5_chebyshev
-- name    : QuantumMC.MeanEst.theorem_5_chebyshev
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:27:04.439713+00:00
-- url     : https://prove2.me/theorems/bb61c725-4f2d-4a2b-be6a-39c460645c56
-- title:
--   §2.3, proof of Theorem 5 — Chebyshev bound
-- statement:
--   Let $X$ have variance at most $\sigma^2$, with $\sigma>0$, and let $\mu'=\mathbb E[X/\sigma]$. Then
--
--   $$\Pr(|X/\sigma-\mu'|\ge3)\le\frac19.$$
--
--   This bounds the chance that Algorithm 3's one preliminary sample is far from the rescaled mean. **Formalization Note** Finite variance is expressed with $X\in L^2$ as well as the variance inequality.
-- source:
--   Montanaro, Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, §2.3, proof of Theorem 5, p. 12

import Mathlib
import Definitions.Def_QuantumMC_MeanEst_Setting

namespace QuantumMC.MeanEst

open MeasureTheory ProbabilityTheory

/-- §2.3, proof of Theorem 5, p. 12: Chebyshev at three standard deviations. -/
theorem theorem_5_chebyshev {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hXm : Measurable X)
    (hX : MemLp X 2 P) (σ : ℝ) (hvar : variance X P ≤ σ ^ 2)
    (hσ : 0 < σ) :
    P {ω | 3 ≤ |X ω / σ - ∫ x, X x / σ ∂P|} ≤ (1 / 9 : ENNReal) := by sorry
end QuantumMC.MeanEst
