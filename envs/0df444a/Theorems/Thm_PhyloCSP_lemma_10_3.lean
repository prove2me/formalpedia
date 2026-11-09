-- Prove2me | Theorems.Thm_PhyloCSP_lemma_10_3
-- name    : PhyloCSP.lemma_10_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:24:10.136902+00:00
-- url     : https://prove2.me/theorems/d6ddc5a8-d1ae-4b6b-8f62-44e9a80302e7
-- title:
--   Lemma 10.3 — two orders convex for the same 4-leaf tree
-- statement:
--   Suppose two orders on four leaves are convex for the same rooted binary tree. If the first order is $1,2,3,4$, then the second is neither $2,4,1,3$ nor $3,1,4,2$.
--
--   This combinatorial obstruction drives the comparison of rank partitions of different orders (Lemma 10.4).
--
--   Differences from the source:
--   - encoding: leaves 1, 2, 3, 4 → 0, 1, 2, 3 : Fin 4; orders given by listing the leaves; reason: relabeling
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Lemma 10.3, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_PhyloCSP_Pattern
import Definitions.Def_PhyloCSP_IsConvexOrder

set_option autoImplicit false

namespace PhyloCSP

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027
submission (manuscript sha256 3444b6c0…682dac), Lemma 10.3, p.34 (PDF p.36): "Suppose two orders on
4 leaves are convex for the same binary tree. If the first order is 1, 2, 3, 4, the second cannot be
2, 4, 1, 3 or 3, 1, 4, 2."

**Formalization Note.** Leaves `1, 2, 3, 4` are `0, 1, 2, 3 : Fin 4`; the first order is the usual
order of `Fin 4`; the excluded orders list the leaves as `[1, 3, 0, 2]` and `[2, 0, 3, 1]`
(`orderOfList`). Both exclusions are stated. -/
theorem lemma_10_3 (T : Pattern (Fin 4)) (h : IsConvexOrder T.1 (· < ·)) :
    ¬ IsConvexOrder T.1 (orderOfList [1, 3, 0, 2]) ∧
      ¬ IsConvexOrder T.1 (orderOfList [2, 0, 3, 1]) := by sorry

end PhyloCSP
