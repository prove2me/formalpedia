-- Prove2me | Theorems.Thm_QuantumMC_MeanEst_lemma_4_tail_bound
-- name    : QuantumMC.MeanEst.lemma_4_tail_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:36.778633+00:00
-- url     : https://prove2.me/theorems/2432f101-f2b0-436c-9291-69a016866a11
-- title:
--   §2.2, proof of Lemma 4 — tail second-moment bound
-- statement:
--   Let $X$ be nonnegative with a finite second moment. For any natural number $k$,
--
--   $$\mathbb E[X_{[2^k,\infty)}]\le\frac{\|X\|_2^2}{2^k}.$$
--
--   This controls the output omitted by the finite dyadic sum. **Formalization Note** The paper writes a sum over its discrete output law; the integral has the same value for that law.
-- source:
--   Montanaro, Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, §2.2, proof of Lemma 4, p. 10

import Mathlib
import Definitions.Def_QuantumMC_MeanEst_Setting

namespace QuantumMC.MeanEst

open MeasureTheory ProbabilityTheory

/-- §2.2, proof of Lemma 4, p. 10: the dyadic tail is bounded by its second moment. -/
theorem lemma_4_tail_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P)
    (hpos : ∀ ω, 0 ≤ X ω) (k : ℕ) :
    (∫ ω, truncGe ((2 : ℝ) ^ k) X ω ∂P) ≤
      l2norm P X ^ 2 / (2 : ℝ) ^ k := by sorry
end QuantumMC.MeanEst
