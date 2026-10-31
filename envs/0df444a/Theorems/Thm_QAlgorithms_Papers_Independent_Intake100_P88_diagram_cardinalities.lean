-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P88_diagram_cardinalities
-- name    : QAlgorithms.Papers.Independent.Intake100.P88.diagram_cardinalities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:34:25.27824+00:00
-- url     : https://prove2.me/theorems/2782e8b3-6846-43f5-9569-2d82b534edb8
-- title:
--   Unnumbered (1.9): diagram cardinalities
-- statement:
--   For a positive half-integer $\ell$, let $A_\ell$ be the partition diagrams, $P_\ell$ their planar subset, and $T_{2\ell}$ the planar pairings on two rows of $2\ell$ vertices. For an integer $k\ge1$, let $B_k$ be all pairings and $S_k$ the permutation diagrams. Then
--
--   $$|A_\ell|=B(2\ell),\qquad |P_\ell|=|T_{2\ell}|=\frac{1}{2\ell+1}\binom{4\ell}{2\ell},$$
--   $$|B_k|=\prod_{j=0}^{k-1}(2j+1),\qquad |S_k|=k!.$$
--
--   Here $B(m)$ is the Bell number. At half levels the last top and bottom vertices are required to belong to the same block. The odd product is precisely the paper's convention for $(2k)!!$. These formulas give the diagram-space dimensions.
-- source:
--   Partition Algebras, arXiv:math/0401314v2, PDF p. 5, Unnumbered (1.9): diagram cardinalities

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- All four cardinality formulas, PDF p.5, (1.7) and (1.9).
The paper's `(2k)!!` is the odd product, explicitly used here. -/
theorem diagram_cardinalities :
    (∀ m : ℕ, 0 < m →
      Nat.card (LevelDiagram m) = Nat.bell m ∧
      Nat.card {d : LevelDiagram m // IsPlanar d.val} = Nat.choose (2 * m) m / (m + 1) ∧
      Nat.card {d : PartitionDiagram m // IsPlanar d ∧ IsPairing d} = Nat.choose (2 * m) m / (m + 1)) ∧
    (∀ k : ℕ, 0 < k →
      Nat.card {d : PartitionDiagram k // IsPairing d} = (∏ j ∈ Finset.range k, (2 * j + 1)) ∧
      Nat.card {d : PartitionDiagram k // IsPermutation d} = Nat.factorial k) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P88

end
