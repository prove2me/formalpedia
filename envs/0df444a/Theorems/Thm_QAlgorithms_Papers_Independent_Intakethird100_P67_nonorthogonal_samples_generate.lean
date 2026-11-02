-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_nonorthogonal_samples_generate
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.nonorthogonal_samples_generate
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:52:12.3282+00:00
-- url     : https://prove2.me/theorems/07a4a0a7-f28c-454f-9bfb-a5ae0ed2c72c
-- title:
--   §II A example: pairwise nonorthogonal spanning samples are sufficient
-- statement:
--   Let a finite normalized pure sample family contain a linearly independent subfamily $\{\phi_j\}_{j=1}^d$ with the same span $H_{\rm in}$ as the entire family. Assume that every pair in this subfamily has nonzero complex inner product. Then
--
--   $$\operatorname{Alg}_{\mathbb C}\{\lvert\phi_k\rangle\langle\phi_k\rvert\}_k=\mathcal L(H_{\rm in}).$$
--
--   Extra sample vectors and their linear dependencies are allowed. This is a sufficient identifiability example, not a necessary condition on every emulator input.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 3, §II A example: pairwise nonorthogonal spanning samples are sufficient

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF p.3, Eq.(8): pairwise nonorthogonal independent samples are sufficient,
without imposing their pairwise condition on the general emulator results. -/
theorem nonorthogonal_samples_generate [Nonempty J] (phi : K → EuclideanSpace ℂ I) (s : J ↪ K)
    (hphi : ∀ k, IsState (phi k)) (hind : LinearIndependent ℂ (fun j => phi (s j)))
    (hspan : samplePi (pureSamples (fun j => phi (s j))) = samplePi (pureSamples phi))
    (hoverlap : ∀ j k : J, inner ℂ (phi (s j)) (phi (s k)) ≠ 0) :
    Generates (pureSamples phi) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
