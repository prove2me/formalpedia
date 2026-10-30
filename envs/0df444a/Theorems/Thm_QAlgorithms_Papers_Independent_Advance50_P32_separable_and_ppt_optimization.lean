-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P32_separable_and_ppt_optimization
-- name    : QAlgorithms.Papers.Independent.Advance50.P32.separable_and_ppt_optimization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:24:52.538005+00:00
-- url     : https://prove2.me/theorems/570b8fc4-782d-4545-a8dd-08d9b5d2d27a
-- title:
--   Section 5.2, Eq. (25): exact separable optimization and infinite PPT upper bound
-- statement:
--   Let $s>0$, let $q$ be any measurable nonnegative displacement density of integral one, and let $N$ be any rotationally covariant quantum channel. Form the uniformly and commonly rotated ensemble $\rho_{\xi,\theta}=U_\theta W_\xi\rho_sW_\xi^*U_\theta^*$ and its input-first density operator $E=\mathbb E[N(\rho_{\xi,\theta})\otimes\rho_{\xi,\theta}]$. The maximum average overlap $\bar F$ over all entanglement-breaking channels satisfies
--
--   $$\bar F=\sup_{\substack{\Omega\text{ positive separable bounded}\\\operatorname{Tr}_B\Omega=I_A}}\operatorname{Tr}(E\Omega)\ \le\ \sup_{\substack{\Omega\text{ positive bounded},\ \Omega^\Gamma\ge0\\\operatorname{Tr}_B\Omega=I_A}}\operatorname{Tr}(E\Omega).$$
--
--   The ensemble operator $E$ is positive trace class of trace one. Consequently the objectives are ordinary trace-class pairings. Equality with the PPT relaxation is not asserted for arbitrary priors and noise.
-- source:
--   Squeezing the limit: Quantum benchmarks for the teleportation and storage of squeezed states, arXiv:0808.2260v1, PDF p. 11, Section 5.2, Eq. (25)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P32

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P32

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology TensorProduct

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State IsTraceClassChannel BreaksTraceClassEntanglement
   productCoeff traceSize rotationMeasure)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P35 (tracePair)

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel vacuum realFockTracePair)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section 5.2, p.11, (25): exact separable optimization and infinite PPT upper bound.
Here E is trace class, so the objective is the ordinary trace-class pairing. -/
theorem separable_and_ppt_optimization (s : ℝ) (hs : 0 < s) (q : ℝ × ℝ → ℝ)
    (hq : DisplacementDensity q)
    (N : FockOperatorArray (NumberLabel 1) → FockOperatorArray (NumberLabel 1))
    (hN : RotationCovariantNoise N) :
    IsDensity (ensembleOperator s q N) ∧
    averageBenchmark s q N = separableOptimum (ensembleOperator s q N) ∧
    averageBenchmark s q N ≤ pptOptimum (ensembleOperator s q N) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P32

end
