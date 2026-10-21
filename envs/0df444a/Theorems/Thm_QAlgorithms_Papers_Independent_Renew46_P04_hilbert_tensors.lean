-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_hilbert_tensors
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.hilbert_tensors
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:02:21.445766+00:00
-- url     : https://prove2.me/theorems/fb3db274-d2ee-4b10-898e-7099096d1633
-- title:
--   Unnumbered consequence of Proposition 3.8
-- statement:
--   Projective norm attainment means a convergent, absolutely norm-summable bounded tensor series whose cost equals the projective norm.
--
--   Let $H$ be any complete complex Hilbert space. Then
--
--   $$
--   \mathrm{NA}_\pi(H\widehat\otimes_\pi H)=H\widehat\otimes_\pi H.
--   $$
--
--   This is the source’s explicit tensor consequence of Proposition 3.8. No incorrectly complex-linear Riesz map is used as an identification.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 9, Unnumbered consequence of Proposition 3.8

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04

noncomputable section

set_option synthInstance.maxSize 8192

namespace QAlgorithms.Papers.Independent.Renew46.P04

open Filter Set

open scoped Topology TensorProduct ENNReal

universe u v

variable {K : Type*} [RCLike K]

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

/-- PDF pp.9,23: all tensors in H tensor H attain, without separability or nonzero assumptions.
No complex-linear Riesz identification is assumed. -/
theorem hilbert_tensors (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : ∀ z : Projective ℂ H H, TensorAttains z := by sorry

end QAlgorithms.Papers.Independent.Renew46.P04

end
