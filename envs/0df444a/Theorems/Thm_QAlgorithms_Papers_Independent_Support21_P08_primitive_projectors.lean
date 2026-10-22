-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_primitive_projectors
-- name    : QAlgorithms.Papers.Independent.Support21.P08.primitive_projectors
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:27:56.84426+00:00
-- url     : https://prove2.me/theorems/6357d095-fca6-4e76-b1e8-84396a5d6d92
-- title:
--   Primitive tableau and central shape idempotents
-- statement:
--   Let $K$ be a field and $A$ a unital cellular $K$-algebra with finite cell datum $(\Lambda,T,a)$, ordered tableau sets, and exact index-swapping involution. Let $L_1,\ldots,L_M$ be commuting, involution-fixed JM elements with triangular-action contents $c_t(i)$. Assume that the complete content sequences distinguish all tableaux, including tableaux of different shapes. Define $F_t$ by the interpolation product of Definition 3.1, $f_{st}=F_s a_{st}F_t$, and $\gamma_t$ as the coefficient of $a_{tt}$ in $f_{tt}^2$. Assume every cell has a tableau. Each $F_t$ is a nonzero primitive algebra idempotent, and each $F_\lambda=\sum_{t\in T(\lambda)}F_t$ is a nonzero primitive central idempotent. Both families are complete and pairwise orthogonal, and
--
--   $$F_t=\gamma_t^{-1}f_{tt},\qquad\sum_tF_t=1=\sum_\lambda F_\lambda.$$
--
--   Primitivity in the centre does not assert that a full matrix-block identity is primitive in the algebra.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 13, 3.16

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

/-- Theorem 3.16(a–c), PDF pp.13–14. Primitive central and primitive
algebra idempotents are distinct predicates and both require nonzero.
All cell shapes are nonempty. Separation uses the corrected injective reading. -/
theorem primitive_projectors (J : JMFamily D M) (hsep : separatesAll J)
    (hne : ∀ l, Nonempty (T l)) :
    (∀ t : CellTableau Shape T,
      jmSpectralProjector J t = (seminormalGamma J t)⁻¹ • seminormal J ⟨t.1, (t.2, t.2)⟩ ∧
      PrimitiveIdempotent (jmSpectralProjector J t)) ∧
    (∀ l, PrimitiveCentralIdempotent (shapeProjector J l)) ∧
    CompleteOrthogonalIdempotents (jmSpectralProjector J) ∧ CompleteOrthogonalIdempotents (shapeProjector J) := by sorry

end SeparatedDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
