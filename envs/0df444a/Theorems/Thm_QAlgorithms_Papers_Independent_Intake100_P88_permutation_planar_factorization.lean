-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P88_permutation_planar_factorization
-- name    : QAlgorithms.Papers.Independent.Intake100.P88.permutation_planar_factorization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:33:25.999003+00:00
-- url     : https://prove2.me/theorems/a6121826-1490-4bec-8143-9f107d184b2c
-- title:
--   Unnumbered (1.6): permutation-planar factorization
-- statement:
--   Let $k\ge1$ and let $d$ be a partition diagram on two rows of $k$ vertices. There are permutations $\sigma,\tau\in S_k$ and a planar partition diagram $p$ such that
--
--   $$d=\sigma\circ p\circ\tau.$$
--
--   Composition stacks the left factor above the right factor. Planarity means that the blocks form a noncrossing partition in the clockwise boundary order. The factorization is not asserted to be unique. It reduces diagram calculations to permutations and planar diagrams.
-- source:
--   Partition Algebras, arXiv:math/0401314v2, PDF p. 5, Unnumbered (1.6): permutation-planar factorization

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- Permutation--planar factorization, PDF p.5, equation (1.6); no uniqueness asserted. -/
theorem permutation_planar_factorization (k : ℕ) (_hk : 0 < k) (d : PartitionDiagram k) :
    ∃ s t : Equiv.Perm (Fin k), ∃ p : PartitionDiagram k,
      IsPlanar p ∧ d = diagramCompose (diagramCompose (permutationDiagram s) p)
        (permutationDiagram t) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P88

end
