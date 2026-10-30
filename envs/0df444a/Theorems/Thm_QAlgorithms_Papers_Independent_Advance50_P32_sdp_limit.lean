-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P32_sdp_limit
-- name    : QAlgorithms.Papers.Independent.Advance50.P32.sdp_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:27:35.665476+00:00
-- url     : https://prove2.me/theorems/2f6c684c-b0d0-4f33-b814-2e1ac9792ff6
-- title:
--   Section 5.2, unnumbered limiting SDP statement
-- statement:
--   Fix $s>0$, a measurable nonnegative probability density $q$ for displacement, and a rotationally covariant quantum channel $N$. Let $E$ be the corresponding commonly rotated input-first ensemble density. Write $V_c$ for the finite rectangular PPT optimum of $\operatorname{Tr}(\Omega P_cEP_c)$ with marginal at most identity, and $V_\infty$ for the bounded infinite-dimensional PPT optimum with marginal equal to identity. Then the paper's asserted large-cutoff limit is
--
--   $$\lim_{c\to\infty}\bigl(V_c+1-\operatorname{Tr}(P_cEP_c)\bigr)=V_\infty.$$
--
--   Here $P_c$ is the triangular total-number cutoff and the finite optimization acts on photon numbers $0,\ldots,c$ in each mode. This is convergence to the infinite PPT relaxation; no rate, finite exact termination, equality with the EB optimum, or complexity bound is asserted.
-- source:
--   Squeezing the limit: Quantum benchmarks for the teleportation and storage of squeezed states, arXiv:0808.2260v1, PDF p. 12, Section 5.2, large-cutoff clause before Theorem 5

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

/-- Section 5.2, p.12: only the asserted large-cutoff limit to the infinite PPT bound.
No convergence rate, exact finite termination, or computational complexity is claimed. -/
theorem sdp_limit (s : ℝ) (hs : 0 < s) (q : ℝ × ℝ → ℝ)
    (hq : DisplacementDensity q)
    (N : FockOperatorArray (NumberLabel 1) → FockOperatorArray (NumberLabel 1))
    (hN : RotationCovariantNoise N) :
    Tendsto (fun c => certifiedBound c (ensembleOperator s q N)) atTop
      (nhds (pptOptimum (ensembleOperator s q N))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P32

end
