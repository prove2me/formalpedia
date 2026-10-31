-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P88_preceding_generator_factorization
-- name    : QAlgorithms.Papers.Independent.Intake100.P88.preceding_generator_factorization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:36:14.078543+00:00
-- url     : https://prove2.me/theorems/6903ed64-11d5-472a-b826-66af42d28efb
-- title:
--   Unnumbered (2.15): factorization through the preceding generator
-- statement:
--   Write $\ell=m/2$ and let $I_\ell$ be the diagrams with fewer than $\lceil\ell\rceil$ physical propagating blocks, counting the distinguished block at half levels. The deficient diagram sets at levels $0$ and $1/2$ are empty. For every $\ell\ge1$,
--
--   $$I_\ell=\{a\,p_\ell\,b:a,b\in A_{\ell-1/2}\},$$
--
--   where the factors are included by the canonical preceding-level inclusion and multiplication is diagram stacking. At integer levels $p_\ell$ isolates the last top and bottom vertices; at half levels it merges the last two vertical columns. This gives the exact preceding-level factorization, without replacing the factors by elements of the larger ambient monoid.
-- source:
--   Partition Algebras, arXiv:math/0401314v2, PDF p. 11, Unnumbered (2.15): factorization through the preceding generator

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- Factorization through the preceding generator and precisely the preceding level,
PDF p.11, (2.15). SOURCE BOUNDARY CORRECTION: the displayed construction starts
at level one; the level-zero and level-one-half deficient sets are empty. -/
theorem preceding_generator_factorization :
    (∀ m : ℕ, m ≤ 1 → deficientDiagrams m = ∅) ∧
    (∀ m : ℕ, 2 ≤ m → deficientDiagrams m =
      {d : LevelDiagram m | ∃ a b : LevelDiagram (m - 1),
        d.val = diagramCompose
          (diagramCompose (precedingDiagram m a) (precedingGenerator m)) (precedingDiagram m b)}) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P88

end
