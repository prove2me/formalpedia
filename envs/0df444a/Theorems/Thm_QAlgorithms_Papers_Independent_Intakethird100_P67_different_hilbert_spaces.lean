-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_different_hilbert_spaces
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.different_hilbert_spaces
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:58:16.538802+00:00
-- url     : https://prove2.me/theorems/a0cb15ca-1144-4977-a562-d273dcae9f15
-- title:
--   §III remarks: matching Gram matrices in distinct input and output spaces
-- statement:
--   Let two normalized sample families, $K\ge2$, lie in possibly different finite-dimensional complex Hilbert spaces and have the same complex Gram matrix. Assume the input samples generate the full algebra on their span. Then there is a partial isometry $M$ matching every input sample to its corresponding output sample, with
--
--   $$M^\dagger M=\Pi_{\rm in},\qquad MM^\dagger=\Pi_{\rm out}.$$
--
--   It restricts to a unitary between the two sample spans. The emulator constructed from these two families converges uniformly on supported input density operators to $\rho\mapsto M\rho M^\dagger$ in trace distance. Gram equality concerns consistent vector representatives; physical density records alone need not reveal those phases. No equality of ambient dimensions is required.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 4, §III remarks: matching Gram matrices in distinct input and output spaces

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF p.4: equal complex Gram matrices specify a unitary between the sample spans,
represented by a partial isometry between potentially different ambient dimensions. -/
theorem different_hilbert_spaces (phi : K → EuclideanSpace ℂ I) (chi : K → EuclideanSpace ℂ J) (a : K)
    (hK : 2 ≤ Fintype.card K) (hphi : ∀ k, IsState (phi k))
    (hchi : ∀ k, IsState (chi k)) (hgen : Generates (pureSamples phi))
    (hgram : ∀ j k, inner ℂ (phi j) (phi k) = inner ℂ (chi j) (chi k)) :
    ∃ M : Matrix J I ℂ, Mᴴ * M = samplePi (pureSamples phi) ∧
      M * Mᴴ = samplePi (pureSamples chi) ∧
      (∀ k, Matrix.toEuclideanLin M (phi k) = chi k) ∧
      ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ T ≥ N, ∀ rho : Matrix I I ℂ,
        IsDensityMatrix rho → InSampleSupport (pureSamples phi) rho →
        traceDistance (traceRight (jointEmulator (nonanchorProbability a)
          (erasureGate phi a) (erasureGate chi a) (phi a) (chi a) T rho))
          (M * rho * Mᴴ) ≤ eps := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
