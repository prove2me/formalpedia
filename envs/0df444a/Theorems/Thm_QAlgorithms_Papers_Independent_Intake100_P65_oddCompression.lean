-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_oddCompression
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.oddCompression
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:13:56.061986+00:00
-- url     : https://prove2.me/theorems/63a0d70d-dcf5-40c0-b5be-c593df04c799
-- title:
--   Odd loop-parameter relation with the contraction factor
-- statement:
--   Let $R$ be a commutative unital ring with $2$ invertible, let $n\ge2$, and let $\Omega$ be any scalar sequence. For every $a\ge0$, in $W_n^{\mathrm{aff}}(\Omega)$,
--
--   $$\omega_{2a+1}E_1=\frac12\left(-\omega_{2a}+\sum_{b=1}^{2a+1}(-1)^{b-1}\omega_{b-1}\omega_{2a+1-b}\right)E_1.$$
--
--   This records the restriction forced by the unwrapping relations without cancelling a possibly torsion contraction.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 5, Corollary 2.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Corollary 2.4, PDF p.5. The E_1 factor is retained over rings with torsion;
there is no scalar admissibility assumption or cancellation. -/
theorem oddCompression (R : Type u) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (n : ℕ) (hn : 2 ≤ n) (a : ℕ) :
    omega (2*a+1) • affineE R omega n 0 =
      (⅟ (2 : R) * (-omega (2*a) +
        ∑ b ∈ Finset.range (2*a+1), (-1 : R)^b * omega b * omega (2*a-b))) •
          affineE R omega n 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
