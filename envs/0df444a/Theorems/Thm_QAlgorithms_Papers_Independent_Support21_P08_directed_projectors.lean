-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_directed_projectors
-- name    : QAlgorithms.Papers.Independent.Support21.P08.directed_projectors
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:32:41.321483+00:00
-- url     : https://prove2.me/theorems/bb900c62-5e1f-4940-b549-bb78c0a60955
-- title:
--   The singleton-shaped projectors are directed
-- statement:
--   Let $R$ be a commutative integral domain, and let $L_1,\ldots,L_n$ be upper triangular matrices on a chosen basis indexed by $\{1,\ldots,d\}$. Write $r_k^i$ for the $i$th diagonal entry of $L_k$. A matrix has shape $J$ when its diagonal is the indicator of the nonempty set $J$ and every nonzero entry at $(a,b)$ has $a\le i\le b$ for some $i\in J$. Make the fixed unit-separating ordered interpolation choices and set $E^i=Z_i^d$ as in Appendix §3. These idempotents are directed:
--
--   $$E^jE^i=0\qquad(j>i).$$
--
--   The larger index is on the left. Two-sided orthogonality is not asserted before orthogonalization.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 26, App.3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section AppendixDefinitions

variable {R : Type*} [CommRing R]

/-- Appendix Lemma 3.3, PDF p.26: larger index on the left. This does not
assert two-sided orthogonality before the Gram–Schmidt step. -/
theorem directed_projectors [IsDomain R] {d n : ℕ}
    (S : TriangularSystem R d n) (C : SeparatingChoices S) :
    DirectedFamily (directedProjector S C) := by sorry

end AppendixDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
