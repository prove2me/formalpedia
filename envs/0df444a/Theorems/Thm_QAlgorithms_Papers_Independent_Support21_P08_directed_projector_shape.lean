-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_directed_projector_shape
-- name    : QAlgorithms.Papers.Independent.Support21.P08.directed_projector_shape
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:32:15.849756+00:00
-- url     : https://prove2.me/theorems/09983033-d7d6-48a5-ae18-ffa934bed06b
-- title:
--   The ordered interpolation power has singleton shape
-- statement:
--   Let $R$ be a commutative integral domain, and let $L_1,\ldots,L_n$ be upper triangular matrices on a chosen basis indexed by $\{1,\ldots,d\}$. Write $r_k^i$ for the $i$th diagonal entry of $L_k$. A matrix has shape $J$ when its diagonal is the indicator of the nonempty set $J$ and every nonzero entry at $(a,b)$ has $a\le i\le b$ for some $i\in J$. For each distinct $i,j$, choose a position $k(i,j)$ whose diagonal difference $r_{k(i,j)}^i-r_{k(i,j)}^j$ is a unit, and fix an order of $j\ne i$. Put
--
--   $$Z_i=\prod_{j\ne i}^{\mathrm{ordered}}\frac{L_{k(i,j)}-r_{k(i,j)}^jI}{r_{k(i,j)}^i-r_{k(i,j)}^j},\qquad E^i=Z_i^d.$$
--
--   Then $E^i$ is an idempotent of shape $\{i\}$. Operators are not assumed to commute.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 25, App.3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section AppendixDefinitions

variable {R : Type*} [CommRing R]

/-- Appendix Lemma 3.1, PDF pp.25–26: E^i is an idempotent of shape {i}.
The chosen factors are ordered and need not commute. -/
theorem directed_projector_shape [IsDomain R] {d n : ℕ}
    (S : TriangularSystem R d n) (C : SeparatingChoices S) (i : Fin d) :
    directedProjector S C i * directedProjector S C i = directedProjector S C i ∧
    HasShape (directedProjector S C i) {i} := by sorry

end AppendixDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
