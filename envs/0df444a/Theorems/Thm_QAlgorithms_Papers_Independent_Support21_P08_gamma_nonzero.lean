-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_gamma_nonzero
-- name    : QAlgorithms.Papers.Independent.Support21.P08.gamma_nonzero
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:25:19.082785+00:00
-- url     : https://prove2.me/theorems/b21f7e0c-3897-41a0-87a9-2ca743b633d4
-- title:
--   Seminormal structure coefficients do not vanish
-- statement:
--   Let $K$ be a field and $A$ a unital cellular $K$-algebra with finite cell datum $(\Lambda,T,a)$, ordered tableau sets, and exact index-swapping involution. Let $L_1,\ldots,L_M$ be commuting, involution-fixed JM elements with triangular-action contents $c_t(i)$. Assume that the complete content sequences distinguish all tableaux, including tableaux of different shapes. Define $F_t$ by the interpolation product of Definition 3.1, $f_{st}=F_s a_{st}F_t$, and $\gamma_t$ as the coefficient of $a_{tt}$ in $f_{tt}^2$. Every tableau has a nonzero seminormal structure coefficient:
--
--   $$\gamma_t\ne0\qquad(t\in T(\Lambda)).$$
--
--   This is a conclusion needed to normalize primitive idempotents; nondegeneracy is not assumed.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 11, 3.9

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

/-- Corollary 3.9, PDF pp.11–12. Complete-sequence injectivity is the
proof-intended correction of printed Definition 2.8. -/
theorem gamma_nonzero (J : JMFamily D M) (hsep : separatesAll J) :
    ∀ t : CellTableau Shape T, seminormalGamma J t ≠ 0 := by sorry

end SeparatedDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
