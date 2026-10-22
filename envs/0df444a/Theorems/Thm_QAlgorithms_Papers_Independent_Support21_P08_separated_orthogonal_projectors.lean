-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_separated_orthogonal_projectors
-- name    : QAlgorithms.Papers.Independent.Support21.P08.separated_orthogonal_projectors
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:33:35.134914+00:00
-- url     : https://prove2.me/theorems/2d7fd125-6cdc-4fa3-9857-36ac367ceb33
-- title:
--   Separated triangular matrices yield complete singleton projectors
-- statement:
--   Let $R$ be a commutative integral domain, and let $L_1,\ldots,L_n$ be upper triangular matrices on a chosen basis indexed by $\{1,\ldots,d\}$. Write $r_k^i$ for the $i$th diagonal entry of $L_k$. A matrix has shape $J$ when its diagonal is the indicator of the nonempty set $J$ and every nonzero entry at $(a,b)$ has $a\le i\le b$ for some $i\in J$. Assume that every pair $i\ne j$ has a position $k$ with $r_k^i-r_k^j\in R^\times$. There exist matrices $e_1,\ldots,e_d$ of shape $\{i\}$ in the represented algebra $R[L_1,\ldots,L_n]$ such that
--
--   $$e_i^2=e_i,\qquad e_ie_j=0\ (i\ne j),\qquad\sum_i e_i=I.$$
--
--   The conclusion concerns the matrix image, including the empty-dimensional convention, and does not assert absolute irreducibility of an arbitrary original module.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 27, App.4.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section AppendixDefinitions

variable {R : Type*} [CommRing R]

/-- Appendix Proposition 4.2, PDF p.27. All singleton shapes and membership
in the generated matrix algebra are retained, as in the proof. The original
module is not asserted absolutely irreducible. Empty d gives the empty family. -/
theorem separated_orthogonal_projectors [IsDomain R] {d n : ℕ}
    (S : TriangularSystem R d n) (hsep : UnitSeparating S) :
    ∃ e : Fin d → Matrix (Fin d) (Fin d) R,
      CompleteOrthogonalIdempotents e ∧ ∀ i, HasShape (e i) {i} ∧ e i ∈ representedAlgebra S := by sorry

end AppendixDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
