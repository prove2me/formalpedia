-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_skeinPower
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.skeinPower
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:13:33.846025+00:00
-- url     : https://prove2.me/theorems/ea158ddd-b076-49f9-af4d-a9abed979975
-- title:
--   Power skein identity
-- statement:
--   Let $R,n,\Omega$ be as in 2.2. For $1\le i<n$ and $a\ge1$, in the affine algebra one has
--
--   $$S_iX_i^a=X_{i+1}^aS_i+\sum_{b=1}^aX_{i+1}^{b-1}(E_i-1)X_i^{a-b}.$$
--
--   The order of these noncommuting factors is part of the formula. This is the power form of the skein relation.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 4, Lemma 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Lemma 2.3, PDF pp.4--5: the full power skein formula. -/
theorem skeinPower (R : Type u) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (n i a : ℕ) (hn : 1 ≤ n)
    (hi : i+1 < n) (ha : 1 ≤ a) :
    affineS R omega n i * affineX R omega n i ^ a =
      affineX R omega n (i+1) ^ a * affineS R omega n i +
        ∑ b ∈ Finset.Icc 1 a, affineX R omega n (i+1) ^ (b-1) *
          (affineE R omega n i - 1) * affineX R omega n i ^ (a-b) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
