-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P32_phase_covariant_characterization
-- name    : QAlgorithms.Papers.Independent.Advance50.P32.phase_covariant_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:20:32.883994+00:00
-- url     : https://prove2.me/theorems/15696591-f02a-4af7-a388-6b4a367f8d9a
-- title:
--   Appendix A, Lemma 3 (Phase space covariant channels)
-- statement:
--   Consider the full $n$-mode bosonic system, including the scalar case $n=0$. A channel $T$ is phase-space covariant if it intertwines conjugation by every Weyl displacement on every trace-class input. Such a channel has a unique classical characteristic function $f$ for which
--
--   $$T^*(W_\xi)=f(\xi)W_\xi.$$
--
--   Here $f(\xi)=\int e^{-i\xi\cdot\sigma\zeta}\,d\mu(\zeta)$ for an arbitrary probability measure $\mu$ on real phase space; $\sigma$ is the canonical symplectic form. Conversely every such $f$ determines a phase-space covariant channel, uniquely on all trace-class inputs. The adjoint identity is expressed by trace duality against every complex trace-class operator. This characterizes arbitrary covariant channels, without a Gaussian restriction; the paper supplies a proof of a characterization previously used in [25,26].
-- source:
--   Squeezing the limit: Quantum benchmarks for the teleportation and storage of squeezed states, arXiv:0808.2260v1, PDF p. 17, Appendix A, Lemma 3, Eq. (A.2)

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

/-- Appendix A, Lemma 3, p.17: both directions and uniqueness on trace class.
Previously used in [25,26]; this paper supplies a proof. Zero modes are allowed. -/
theorem phase_covariant_characterization (n : ℕ) :
    (∀ T : FockOperatorArray (NumberLabel n) → FockOperatorArray (NumberLabel n),
      IsTraceClassChannel T → PhaseCovariant T →
      ∃! f : QuadraturePoint n → ℂ, ClassicalCharacteristic f ∧ WeylMultiplier T f) ∧
    (∀ f : QuadraturePoint n → ℂ, ClassicalCharacteristic f →
      ∃ T : FockOperatorArray (NumberLabel n) → FockOperatorArray (NumberLabel n),
        IsTraceClassChannel T ∧ PhaseCovariant T ∧ WeylMultiplier T f ∧
        ∀ S : FockOperatorArray (NumberLabel n) → FockOperatorArray (NumberLabel n),
          IsTraceClassChannel S → PhaseCovariant S → WeylMultiplier S f →
          ∀ X, IsTraceClass X → S X = T X) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P32

end
