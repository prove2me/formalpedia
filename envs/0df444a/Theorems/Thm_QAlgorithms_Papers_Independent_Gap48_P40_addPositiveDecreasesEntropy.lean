-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_addPositiveDecreasesEntropy
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.addPositiveDecreasesEntropy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:30:10.195587+00:00
-- url     : https://prove2.me/theorems/22a4b7b6-69fc-49de-baff-7a74947be225
-- title:
--   §VII.B, Lemma 11: adding the same positive operator decreases relative entropy
-- statement:
--   Let $A,B,C$ be arbitrary positive semidefinite complex matrices on the same positive finite-dimensional space. They need not be normalized. With signed support-aware Umegaki relative entropy,
--
--   $$
--   D(A+C\|B+C)\le D(A\|B).
--   $$
--
--   Adding the same positive operator to both arguments decreases this unnormalized relative entropy.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 10, §VII.B, Lemma 11: adding the same positive operator decreases relative entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

/-- PDF p.10, Lemma 11: unnormalized PSD arguments and signed extended entropy. -/
theorem addPositiveDecreasesEntropy {d : ℕ} (hd : 0 < d) (A B C : Mat d)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) :
    relativeEntropy (A + C) (B + C) ≤ relativeEntropy A B := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
