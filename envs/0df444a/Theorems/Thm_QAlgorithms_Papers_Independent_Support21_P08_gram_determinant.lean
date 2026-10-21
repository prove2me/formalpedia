-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_gram_determinant
-- name    : QAlgorithms.Papers.Independent.Support21.P08.gram_determinant
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:19:49.071378+00:00
-- url     : https://prove2.me/theorems/c421c9e5-6413-41c3-8b60-cdfd1ace41ba
-- title:
--   Gram determinants are products of seminormal structure coefficients
-- statement:
--   Let $K$ be a field and $A$ a unital cellular $K$-algebra with finite cell datum $(\Lambda,T,a)$, ordered tableau sets, and exact index-swapping involution. Let $L_1,\ldots,L_M$ be commuting, involution-fixed JM elements with triangular-action contents $c_t(i)$. Assume that the complete content sequences distinguish all tableaux, including tableaux of different shapes. Define $F_t$ by the interpolation product of Definition 3.1, $f_{st}=F_s a_{st}F_t$, and $\gamma_t$ as the coefficient of $a_{tt}$ in $f_{tt}^2$. For each shape $\lambda$, let $G(\lambda)$ be the determinant of the original cell Gram matrix. Then
--
--   $$G(\lambda)=\prod_{t\in T(\lambda)}\gamma_t.$$
--
--   This is the determinant consequence, independently retained from the invalid mixed-pairing assertion in the full numbered Theorem 3.12.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 1, Abstract; Theorem 3.12 determinant consequence

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

/-- Abstract headline promised in the abstract (PDF p.1), determinant consequence
of Theorem 3.12 (PDF pp.12–13). Separation uses injective complete content
sequences, correcting the weaker comparable-pair predicate printed in 2.8.
Neither nondegeneracy nor the seminormalGamma multiplication formula is a hypothesis. -/
theorem gram_determinant (J : JMFamily D M) (hsep : separatesAll J) (l : Shape) :
    gramDet D l = ∏ t : T l, seminormalGamma J ⟨l, t⟩ := by sorry

end SeparatedDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
