-- Prove2me | Theorems.Thm_Problem97_six_mul_card_add_one_le_iCount_of_K4_of_iCountAt_ge_seven
-- name    : Problem97.six_mul_card_add_one_le_iCount_of_K4_of_iCountAt_ge_seven
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-13T02:36:51.861796+00:00
-- url     : https://prove2.me/theorems/f78ca3e6-9ade-4143-be6e-963a5788ef5b
-- title:
--   One vertex with an extra local pair raises the total count
-- statement:
--   If every point of a finite planar set has four equidistant neighbours, and one point has at least seven local isosceles pairs, then six times the number of points plus one is at most the total isosceles count.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/bd8528ea10a12da2c84a10cc5897e36681c2e75d/lean/Erdos9796Proof/P97/IsoscelesCount.lean#L166-L189

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
# Strict total isosceles count lower bound from one excess apex

Under the counting convention used by Dumitrescu (2006), four equidistant
neighbors at every vertex give the baseline `6 * A.card ≤ iCount A`. If one
vertex contributes at least seven isosceles pairs, the total rises to
`6 * A.card + 1 ≤ iCount A`.

The statement is rehosted from
`Erdos9796Proof.P97.IsoscelesCount` at source commit
`bd8528ea10a12da2c84a10cc5897e36681c2e75d`.

The counting method is attributed to Dumitrescu (2006); the Lean
formalization is by Adam McKenna.
-/

theorem Problem97.six_mul_card_add_one_le_iCount_of_K4_of_iCountAt_ge_seven
    {A : Finset ℝ²} (hK4 : HasNEquidistantProperty 4 A) {p : ℝ²} (hpA : p ∈ A)
    (hpExtra : 7 ≤ iCountAt A p) :
    6 * A.card + 1 ≤ iCount A := by sorry
