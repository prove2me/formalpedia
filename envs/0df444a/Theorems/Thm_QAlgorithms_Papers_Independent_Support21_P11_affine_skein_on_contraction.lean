-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P11_affine_skein_on_contraction
-- name    : QAlgorithms.Papers.Independent.Support21.P11.affine_skein_on_contraction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:58:00.584974+00:00
-- url     : https://prove2.me/theorems/a23fe237-0e28-49d3-b35c-4f925f9e4ef0
-- title:
--   Affine skein power acting on the contraction
-- statement:
--   Let $R$ be a commutative ring with identity, $\omega=(\omega_a)_{a\ge0}$ any sequence in $R$, and $n\ge2$. In $W_n^{\mathrm{aff}}(\omega)$, for every integer $a\ge1$,
--
--   $$
--   s_1x_1^ae_1=(-1)^ax_1^ae_1+\sum_{b=1}^a(-1)^{b-1}\omega_{a-b}x_1^{b-1}e_1-\delta_{a\text{ odd}}x_1^{a-1}e_1.
--   $$
--
--   Here $\delta$ is the indicator, and scalar coefficients act through the ground ring. This records the contraction form of the iterated affine skein identity, without any admissibility assumption.
-- source:
--   Admissibility Conditions for Degenerate Cyclotomic BMW Algebras, arXiv:0905.4253v2, PDF p. 3, Lemma 2.6

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Lemma 2.6, equation (2.5), PDF p.3; the last term is subtracted. -/
theorem affine_skein_on_contraction (R : Type*) [CommRing R] (omega : ℕ → R)
    (n a : ℕ) (hn : 2 ≤ n) (ha : 1 ≤ a) :
    affineS R omega n 0 * affineX R omega n 0 ^ a * affineE R omega n 0 =
      (-1 : R) ^ a • (affineX R omega n 0 ^ a * affineE R omega n 0) +
      (∑ b ∈ Finset.Icc 1 a, ((-1 : R) ^ (b - 1) * omega (a - b)) •
        (affineX R omega n 0 ^ (b - 1) * affineE R omega n 0)) -
      (if Odd a then affineX R omega n 0 ^ (a - 1) * affineE R omega n 0 else 0) := by sorry

end QAlgorithms.Papers.Independent.Support21.P11

end
