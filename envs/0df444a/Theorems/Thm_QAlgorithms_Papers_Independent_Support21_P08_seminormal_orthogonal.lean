-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_seminormal_orthogonal
-- name    : QAlgorithms.Papers.Independent.Support21.P08.seminormal_orthogonal
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:26:49.381099+00:00
-- url     : https://prove2.me/theorems/c196df81-567c-4da2-b527-2143069b6fdd
-- title:
--   Orthogonality for the row-sum extension of cell forms
-- statement:
--   Let $K$ be a field and $A$ a unital cellular $K$-algebra with finite cell datum $(\Lambda,T,a)$, ordered tableau sets, and exact index-swapping involution. Let $L_1,\ldots,L_M$ be commuting, involution-fixed JM elements with triangular-action contents $c_t(i)$. Assume that the complete content sequences distinguish all tableaux, including tableaux of different shapes. Define $F_t$ by the interpolation product of Definition 3.1, $f_{st}=F_s a_{st}F_t$, and $\gamma_t$ as the coefficient of $a_{tt}$ in $f_{tt}^2$. Extend the bilinear cell forms to $A$ by making the row summands in the regular-module decomposition mutually orthogonal, sending $f_{st}$ in a row to $a_tF_t$ in $C(\lambda)$. Then the $f_{st}$ form a basis, their diagonal pairings are nonzero, and
--
--   $$\langle f_{st}^{\lambda},f_{uv}^{\mu}\rangle=0\quad\text{for distinct cell-basis indices}. $$
--
--   This is a particular bilinear extension, not an arbitrary bilinear or Hermitian form.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 13, 3.13

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section SeparatedDefinitions

variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]

variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}

variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]

variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

/-- Remark 3.13, PDF p.13. The extension is defined by the row summands,
using bilinear cell forms, not a Hermitian inner product. The false mixed
pairing in 3.12 is not used. Separation is the corrected injective reading. -/
theorem seminormal_orthogonal (J : JMFamily D M) (hsep : separatesAll J) :
    (∃ b : Module.Basis (CellIndex Shape T) K A, ∀ z, b z = seminormal J z) ∧
    (∀ z w : CellIndex Shape T, z ≠ w →
      extendedForm J (seminormal J z) (seminormal J w) = 0) ∧
    (∀ z : CellIndex Shape T, extendedForm J (seminormal J z) (seminormal J z) ≠ 0) := by sorry

end SeparatedDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
