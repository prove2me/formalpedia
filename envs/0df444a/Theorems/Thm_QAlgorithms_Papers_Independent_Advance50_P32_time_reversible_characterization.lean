-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P32_time_reversible_characterization
-- name    : QAlgorithms.Papers.Independent.Advance50.P32.time_reversible_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:21:31.816725+00:00
-- url     : https://prove2.me/theorems/0e525040-9fb7-490f-a05e-f0ddffbca744
-- title:
--   Appendix A, Lemma 4 (Time-reversible channels), corrected using Eq. (15)
-- statement:
--   Let $T$ be a phase-space covariant channel on the full $n$-mode bosonic trace class, with $n\ge0$, and let $\vartheta$ denote linear matrix transposition in the number basis. Then $T\circ\vartheta$ is completely positive if and only if there is a positive trace-class state $\tau$ of trace one such that
--
--   $$T^*(W_\xi)=\operatorname{Tr}[\tau W_{\sqrt2\xi}]\,W_\xi\qquad\text{for every }\xi.$$
--
--   This identifies the time-reversible members of the phase-space covariant channels. The transpose is linear, rather than antiunitary conjugation.
--
--   **Source correction** The printed Eq. (A.5) has $f(\xi/\sqrt2)$. It is changed here to $f(\sqrt2\xi)$, as required both by Eq. (15) on p.6 and the defect symplectic form $2\sigma$ in the Appendix A proof. Vacuum $\tau$ gives covariance noise $2I$, agreeing with the heterodyne channel. Independent moderation of this correction remains required.
-- source:
--   Squeezing the limit: Quantum benchmarks for the teleportation and storage of squeezed states, arXiv:0808.2260v1, PDF p. 18, Appendix A, Lemma 4, corrected by Eq. (15), p.6

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

/-- Appendix A, Lemma 4, p.18, corrected using (15), p.6.
PRINTED: f(xi/sqrt(2)). CHANGED: f(sqrt(2)xi). WHY: defect form 2 sigma and
(15) explicitly specifies Tr[tau W_(sqrt(2)xi)]. Vacuum tau gives noise 2I;
the printed scale gives I/2 and is not time reversible. Transposition is linear.
Independent moderation is required for this source correction. -/
theorem time_reversible_characterization (n : ℕ)
    (T : FockOperatorArray (NumberLabel n) → FockOperatorArray (NumberLabel n))
    (hT : IsTraceClassChannel T) (hcov : PhaseCovariant T) :
    IsTraceClassChannel (fun X => T X.transpose) ↔ ReversibleMultiplier T := by sorry

end QAlgorithms.Papers.Independent.Advance50.P32

end
