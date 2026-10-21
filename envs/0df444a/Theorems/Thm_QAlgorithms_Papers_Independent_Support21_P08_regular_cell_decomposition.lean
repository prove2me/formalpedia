-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_regular_cell_decomposition
-- name    : QAlgorithms.Papers.Independent.Support21.P08.regular_cell_decomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:26:17.203089+00:00
-- url     : https://prove2.me/theorems/d629a390-614e-4e5f-a810-4667b3808b7b
-- title:
--   The regular module decomposes into cell-module rows
-- statement:
--   Let $K$ be a field and $A$ a unital cellular $K$-algebra with finite cell datum $(\Lambda,T,a)$, ordered tableau sets, and exact index-swapping involution. Let $L_1,\ldots,L_M$ be commuting, involution-fixed JM elements with triangular-action contents $c_t(i)$. Assume that the complete content sequences distinguish all tableaux, including tableaux of different shapes. Define $F_t$ by the interpolation product of Definition 3.1, $f_{st}=F_s a_{st}F_t$, and $\gamma_t$ as the coefficient of $a_{tt}$ in $f_{tt}^2$. Every cell form has zero radical, giving the canonical identification $C(\lambda)=D(\lambda)$. As right modules,
--
--   $$A\cong\bigoplus_{\lambda\in\Lambda}C(\lambda)^{\oplus|T(\lambda)|}.$$
--
--   The finite row-indexed product in Lean is this finite direct sum, and its isomorphism intertwines right multiplication. It is not an algebra isomorphism to a product of cell modules.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 12, 3.11

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

/-- Corollary 3.11, PDF p.12. A module decomposition, not an algebra product.
The finite row-indexed product is the displayed finite direct sum, including
|T(lambda)| copies. C=D is the canonical zero-radical identification.
Uses complete content-sequence separation, correcting Definition 2.8. -/
theorem regular_cell_decomposition (J : JMFamily D M) (hsep : separatesAll J) :
    (∀ l, ZeroCellRadical D l) ∧
    ∃ e : A ≃ₗ[K] (∀ r : CellTableau Shape T, T r.1 → K),
      ∀ x a r, e (x * a) r = cellAct D r.1 (e x r) a := by sorry

end SeparatedDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
