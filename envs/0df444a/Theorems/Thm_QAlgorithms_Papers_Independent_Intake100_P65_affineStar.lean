-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_affineStar
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.affineStar
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:12:52.709065+00:00
-- url     : https://prove2.me/theorems/a506d4e8-7ac0-4ffc-ad9d-cc66c7321fa4
-- title:
--   Unique generator-fixing affine anti-involution
-- statement:
--   Let $n\ge1$, let $R$ be a commutative unital ring with $2$ invertible, and let $\Omega$ be any scalar sequence in $R$. The affine algebra $W_n^{\mathrm{aff}}(\Omega)$ has a unique $R$-linear anti-isomorphism $*$ fixing every generator $S_i,E_i$ ($1\le i<n$) and $X_j$ ($1\le j\le n$). It satisfies
--
--   $$(ab)^*=b^*a^*,\qquad (a^*)^*=a.$$
--
--   This equips the specified presentation with its canonical involution.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 4, 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- 2.2, PDF p.4: the unique R-linear generator-fixing anti-isomorphism,
including involutivity. Indices i and j denote source i+1 and j+1. -/
theorem affineStar (R : Type u) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (n : ℕ) (hn : 1 ≤ n) :
    ∃! star : AffineBMW R omega n ≃ₗ[R] AffineBMW R omega n,
      (∀ a b, star (a*b) = star b * star a) ∧
      (∀ i, i+1 < n → star (affineS R omega n i) = affineS R omega n i ∧
        star (affineE R omega n i) = affineE R omega n i) ∧
      (∀ j, j < n → star (affineX R omega n j) = affineX R omega n j) ∧
      Function.Involutive star := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
