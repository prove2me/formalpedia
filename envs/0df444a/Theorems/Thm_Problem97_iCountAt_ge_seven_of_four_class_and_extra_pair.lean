-- Prove2me | Theorems.Thm_Problem97_iCountAt_ge_seven_of_four_class_and_extra_pair
-- name    : Problem97.iCountAt_ge_seven_of_four_class_and_extra_pair
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-13T03:17:18.147987+00:00
-- url     : https://prove2.me/theorems/83338974-c234-4621-af10-fec002d1d6d9
-- title:
--   A four-point class and an extra pair outside it give seven local pairs
-- statement:
--   If T has at least four equidistant neighbours of p and a two-point equal-distance pair has its first point outside T, with both configurations in A.erase p, then the isosceles count at p is at least seven.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/bd8528ea10a12da2c84a10cc5897e36681c2e75d/lean/Erdos9796Proof/P97/IsoscelesCount.lean#L87-L123

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Author: Adam McKenna <adam@mysticflounder.ai>
-/

import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount

open scoped EuclideanGeometry
open Problem97

/-!
# Seven local isosceles pairs from a four-class and an extra pair

A four-point equidistant class supplies six unordered pairs. One further
equal-distance pair outside that class supplies a seventh local isosceles
pair at the same apex.

The statement is rehosted from `Erdos9796Proof.P97.IsoscelesCount` at source
commit `bd8528ea10a12da2c84a10cc5897e36681c2e75d`.

The counting method is attributed to Adrian Dumitrescu (2006); the Lean
formalization is by Adam McKenna.
-/

theorem Problem97.iCountAt_ge_seven_of_four_class_and_extra_pair
    (A : Finset ℝ²) (p : ℝ²) (T : Finset ℝ²) (u v : ℝ²)
    (hTcard : 4 ≤ T.card)
    (hTsub : T ⊆ A.erase p)
    (hTdist : ∃ r : ℝ, ∀ q ∈ T, dist p q = r)
    (hpair_sub : ({u, v} : Finset ℝ²) ⊆ A.erase p)
    (hpair_card : ({u, v} : Finset ℝ²).card = 2)
    (hpair_dist : ∃ r : ℝ, ∀ q ∈ ({u, v} : Finset ℝ²), dist p q = r)
    (hu_not_mem_T : u ∉ T) :
    7 ≤ iCountAt A p := by sorry
