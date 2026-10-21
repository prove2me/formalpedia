-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_hilbert_nuclear
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.hilbert_nuclear
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:01:11.595222+00:00
-- url     : https://prove2.me/theorems/aba60035-3093-49e5-a645-8f04340476fc
-- title:
--   Proposition 3.8: complex Hilbert nuclear operators
-- statement:
--   A nuclear operator and its nuclear norm are defined by the canonical completed-projective quotient described in §2.2.
--
--   Let $H$ be any complete complex Hilbert space. Then
--
--   $$
--   \mathrm{NA}_{\mathcal N}(H,H)=\mathcal N(H,H).
--   $$
--
--   No separability, nonzero-dimension or singular-value expansion is assumed in the statement.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 9, Proposition 3.8: complex Hilbert nuclear operators

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

/-- PDF p.9, Proposition 3.8: all nuclear endomorphisms of an arbitrary complex Hilbert space attain. -/
theorem hilbert_nuclear (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : ∀ T : Nuclear ℂ H H, NuclearAttains T := by sorry

end QAlgorithms.Papers.Independent.Renew46.P04

end
