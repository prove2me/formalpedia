-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_reversible_ideal_cofinite
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.reversible_ideal_cofinite
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:00:46.842993+00:00
-- url     : https://prove2.me/theorems/2b4a4b05-cb6e-45aa-b065-365a978a7653
-- title:
--   Proposition 4.13
-- statement:
--   Let $R$ be any commutative unital ring and let $I$ be an ideal of $R[x,x^{-1}]$. Call $I$ reversible if it contains the image of a monic polynomial in $R[x]$ whose constant coefficient is a unit. Then
--
--   $$
--   I\text{ reversible}\ \Longrightarrow\ R[x,x^{-1}]/I\text{ is finite over }R.
--   $$
--
--   If in addition $R$ is noetherian, the reverse implication also holds. Here finite means finitely generated as an $R$-module, not finite as a set. Neither the unit ideal nor the zero ring is excluded; noetherianness is attached only to the reverse implication.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 16, Proposition 4.13

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Laurent

variable {R : Type u} [CommRing R]

/-- Proposition 4.13, PDF p.16: only the converse requires noetherianness. -/
theorem reversible_ideal_cofinite (I : Ideal (LaurentPolynomial R)) :
    (IsReversibleIdeal I → Module.Finite R (LaurentPolynomial R ⧸ I)) ∧
    (IsNoetherianRing R → Module.Finite R (LaurentPolynomial R ⧸ I) → IsReversibleIdeal I) := by sorry

end Laurent

end QAlgorithms.Papers.Independent.Gap48.P16

end
