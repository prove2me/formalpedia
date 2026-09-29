-- Prove2me | Theorems.Thm_Problem97_iCountAt_ge_ten_of_five_equidistant
-- name    : Problem97.iCountAt_ge_ten_of_five_equidistant
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-13T03:16:55.362911+00:00
-- url     : https://prove2.me/theorems/19834bf2-6bef-454f-b0be-173a27ed6bbd
-- title:
--   Five equidistant neighbours give ten local pairs
-- statement:
--   If S has at least five points in A.erase p at one common distance from p, then the isosceles count at p is at least ten.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/bd8528ea10a12da2c84a10cc5897e36681c2e75d/lean/Erdos9796Proof/P97/IsoscelesCount.lean#L72-L85

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
# Ten local isosceles pairs from five equidistant neighbors

Five equidistant neighbors at one apex force at least ten local isosceles
pairs, the local counting shape used for a fifth point at the same radius.

The statement is rehosted from
`Erdos9796Proof.P97.IsoscelesCount` at source commit
`bd8528ea10a12da2c84a10cc5897e36681c2e75d`.

The counting method is attributed to Adrian Dumitrescu (2006); the Lean
formalization is by Adam McKenna.
-/

theorem Problem97.iCountAt_ge_ten_of_five_equidistant
    (A : Finset ℝ²) (p : ℝ²) (S : Finset ℝ²)
    (hScard : 5 ≤ S.card)
    (hSsub : S ⊆ A.erase p)
    (hSdist : ∃ r : ℝ, ∀ q ∈ S, dist p q = r) :
    10 ≤ iCountAt A p := by sorry
