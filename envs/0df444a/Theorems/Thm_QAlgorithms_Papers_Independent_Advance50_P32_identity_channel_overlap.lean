-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P32_identity_channel_overlap
-- name    : QAlgorithms.Papers.Independent.Advance50.P32.identity_channel_overlap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:23:49.581017+00:00
-- url     : https://prove2.me/theorems/723db4fc-54a3-44a4-ba85-3ab01418fade
-- title:
--   Section 4.2, unnumbered identity-channel overlap
-- statement:
--   Let $s>0$, $\eta\ge0$, and let $\rho_{s,\xi,\theta}$ be any pure squeezed coherent state of the prescribed degree, displacement $\xi\in\mathbb R^2$, and phase $\theta\in[0,2\pi]$. Apply covariance noise $N_\eta$ before the ideal identity storage or teleportation channel. Its overlap with the original pure state is
--
--   $$\operatorname{Tr}[N_\eta(\rho_{s,\xi,\theta})\rho_{s,\xi,\theta}]=\frac{1}{\sqrt{(\eta/2+1/s)(\eta/2+s)}}.$$
--
--   This ideal-device comparison is independent of displacement and phase. At zero noise the overlap is exactly one.
-- source:
--   Squeezing the limit: Quantum benchmarks for the teleportation and storage of squeezed states, arXiv:0808.2260v1, PDF p. 9, Section 4.2, displayed identity overlap after Theorem 2

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

/-- Section 4.2, p.9, formula after Theorem 2: noise precedes the identity device;
zero noise yields overlap one. -/
theorem identity_channel_overlap (s eta : ℝ) (hs : 0 < s) (heta : 0 ≤ eta)
    (xi : ℝ × ℝ) (theta : ℝ) (htheta : theta ∈ Set.Icc 0 (2 * Real.pi)) :
    realFockTracePair (additiveNoise eta (squeezedOrbit s xi theta)) (squeezedOrbit s xi theta) =
      1 / Real.sqrt ((eta / 2 + 1 / s) * (eta / 2 + s)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P32

end
