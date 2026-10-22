-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_linkage_orthogonal_projectors
-- name    : QAlgorithms.Papers.Independent.Support21.P08.linkage_orthogonal_projectors
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:34:17.655986+00:00
-- url     : https://prove2.me/theorems/2890e3b5-8b20-4e37-bc8f-5b9c673e8b86
-- title:
--   Local linkage classes admit complete shaped projectors
-- statement:
--   Let $R$ be a commutative integral domain, and let $L_1,\ldots,L_n$ be upper triangular matrices on a chosen basis indexed by $\{1,\ldots,d\}$. Write $r_k^i$ for the $i$th diagonal entry of $L_k$. A matrix has shape $J$ when its diagonal is the indicator of the nonempty set $J$ and every nonzero entry at $(a,b)$ has $a\le i\le b$ for some $i\in J$. Assume $R$ is also local, and let $J_1,\ldots,J_l$ be the distinct full-residue linkage classes. There exist matrices $e_1,\ldots,e_l\in R[L_1,\ldots,L_n]$, with $e_a$ of shape $J_a$, such that
--
--   $$e_a^2=e_a,\qquad e_ae_b=0\ (a\ne b),\qquad\sum_a e_a=I.$$
--
--   This existential assertion retains the class shapes and generated-algebra content. It does not assert the defective printed nonsingleton interpolation algorithm.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 28, App.6.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section AppendixDefinitions

variable {R : Type*} [CommRing R]

/-- Appendix Proposition 6.1, PDF p.28. This is the existential class-shaped
projector statement, not the flawed printed product Z_J^d. That product has
triangularDiagonalEntry only congruent to 1 on J, and need not be an idempotent. Corrected
interpolation is needed in a future proof; it is not assumed as an input. -/
theorem linkage_orthogonal_projectors [IsDomain R] [IsLocalRing R] {d n : ℕ}
    (S : TriangularSystem R d n) :
    ∃ e : Finset (Fin d) → Matrix (Fin d) (Fin d) R, ClassProjectors S e := by sorry

end AppendixDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
