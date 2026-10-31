-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_evenCompression
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.evenCompression
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:14:20.080237+00:00
-- url     : https://prove2.me/theorems/7d6404d3-6175-4224-bd8e-c669d7402b5f
-- title:
--   Even signed convolution identity
-- statement:
--   For a commutative unital ring $R$ with $2$ invertible, any scalar sequence $\Omega$, and $n\ge2$, the affine algebra satisfies, for $a>0$,
--
--   $$0=\left(\sum_{b=1}^{2a}(-1)^{b-1}\omega_{b-1}\omega_{2a-b}\right)E_1.$$
--
--   The coefficient is the paired even signed convolution appearing in the proof of Corollary 2.4.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 5, Remark 2.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Remark 2.5, PDF pp.5--6: the even signed convolution times E_1. -/
theorem evenCompression (R : Type u) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (n : ℕ) (hn : 2 ≤ n) (a : ℕ) (ha : 0 < a) :
    (0 : AffineBMW R omega n) =
      (∑ b ∈ Finset.range (2*a), (-1 : R)^b * omega b * omega (2*a-1-b)) •
        affineE R omega n 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
