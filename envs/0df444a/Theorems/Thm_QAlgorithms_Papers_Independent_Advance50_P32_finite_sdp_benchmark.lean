-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P32_finite_sdp_benchmark
-- name    : QAlgorithms.Papers.Independent.Advance50.P32.finite_sdp_benchmark
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:19:20.027328+00:00
-- url     : https://prove2.me/theorems/13272f9c-c941-4f4f-ae77-7690d8424b2d
-- title:
--   Theorem 5 (Benchmark—SDP), introduction (iii)
-- statement:
--   Fix $s>0$. Let $q$ be a measurable nonnegative Lebesgue density on $\mathbb R^2$ of integral one, and let $N$ be any rotationally covariant quantum channel. For the input $\rho_{\xi,\theta}=U_\theta W_\xi\rho_sW_\xi^*U_\theta^*$, with phase uniform on $[0,2\pi]$, let $\bar F$ be the maximum average overlap $\operatorname{Tr}[T(N(\rho_{\xi,\theta}))\rho_{\xi,\theta}]$ over all entanglement-breaking $T$. Set $E=\mathbb E[N(\rho_{\xi,\theta})\otimes\rho_{\xi,\theta}]$. Let $Q_j$ project onto total photon number $j$, $P_c=\sum_{j=0}^cQ_j$, and $R_c$ onto photon numbers $0,\ldots,c$ in each factor. Then for every integer $c\ge0$,
--
--   $$\bar F\le\sup\{\operatorname{Tr}(\Omega P_cEP_c):\Omega\in\mathcal B(\operatorname{supp}R_c),\ \Omega\ge0,\ \Omega^\Gamma\ge0,\ \operatorname{Tr}_B\Omega\le I_A\}+1-\operatorname{Tr}(P_cEP_c).$$
--
--   The finite space has dimension $(c+1)^2$. The last term is the omitted probability and makes this a rigorous upper bound. No Gaussian restriction, isotropy of $q$, finite-cutoff equality, or numerical integration error bound is asserted.
-- source:
--   Squeezing the limit: Quantum benchmarks for the teleportation and storage of squeezed states, arXiv:0808.2260v1, PDF p. 12, Theorem 5, Eq. (30)

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

/-- Theorem 5, pp.12–13, (30): rigorous upper bound for any displacement density
and any rotationally covariant channel. No computability, Gaussian restriction,
or numerical quadrature error estimate is assumed. -/
theorem finite_sdp_benchmark (s : ℝ) (hs : 0 < s) (q : ℝ × ℝ → ℝ)
    (hq : DisplacementDensity q)
    (N : FockOperatorArray (NumberLabel 1) → FockOperatorArray (NumberLabel 1))
    (hN : RotationCovariantNoise N) (c : ℕ) :
    averageBenchmark s q N ≤ certifiedBound c (ensembleOperator s q N) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P32

end
