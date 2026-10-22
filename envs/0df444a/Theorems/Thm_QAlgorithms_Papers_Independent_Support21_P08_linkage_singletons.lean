-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_linkage_singletons
-- name    : QAlgorithms.Papers.Independent.Support21.P08.linkage_singletons
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:33:56.787783+00:00
-- url     : https://prove2.me/theorems/c99f820e-8fb1-45b8-b26c-a6a3b1a52e1c
-- title:
--   Local linkage partitions and the singleton separation criterion
-- statement:
--   Let $R$ be a commutative integral domain, and let $L_1,\ldots,L_n$ be upper triangular matrices on a chosen basis indexed by $\{1,\ldots,d\}$. Write $r_k^i$ for the $i$th diagonal entry of $L_k$. A matrix has shape $J$ when its diagonal is the indicator of the nonempty set $J$ and every nonzero entry at $(a,b)$ has $a\le i\le b$ for some $i\in J$. Assume in addition that $R$ is local with maximal ideal $\mathfrak m$. Link indices when their entire diagonal residue sequences agree modulo $\mathfrak m$. Their nonempty classes partition all indices, and
--
--   $$(S)\quad\Longleftrightarrow\quad\text{every linkage class is a singleton}.$$
--
--   The equivalence uses that an element of a local ring is a unit precisely when it lies outside its maximal ideal.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 28, App.5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section AppendixDefinitions

variable {R : Type*} [CommRing R]

/-- Appendix Remark 5.2, PDF p.28. Classes partition all indices, and (S)
is equivalent to their being singletons over the LOCAL domain. -/
theorem linkage_singletons [IsDomain R] [IsLocalRing R] {d n : ℕ}
    (S : TriangularSystem R d n) :
    (∀ J ∈ linkagePartition S, J.Nonempty) ∧
    (∀ J ∈ linkagePartition S, ∀ U ∈ linkagePartition S, J ≠ U → Disjoint J U) ∧
    (∀ i : Fin d, ∃ J ∈ linkagePartition S, i ∈ J) ∧
    (UnitSeparating S ↔ ∀ i : Fin d, linkageClass S i = {i}) := by sorry

end AppendixDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
