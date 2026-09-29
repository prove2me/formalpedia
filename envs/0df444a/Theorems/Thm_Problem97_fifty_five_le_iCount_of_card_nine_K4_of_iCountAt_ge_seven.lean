-- Prove2me | Theorems.Thm_Problem97_fifty_five_le_iCount_of_card_nine_K4_of_iCountAt_ge_seven
-- name    : Problem97.fifty_five_le_iCount_of_card_nine_K4_of_iCountAt_ge_seven
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-13T02:37:21.864112+00:00
-- url     : https://prove2.me/theorems/bef2a1ce-7386-421f-b27f-7c0944082b83
-- title:
--   An extra local pair gives at least fifty-five at nine points
-- statement:
--   If a finite planar set has exactly nine points, every point has four equidistant neighbours, and one point has at least seven local isosceles pairs, then its total isosceles count is at least fifty-five.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/bd8528ea10a12da2c84a10cc5897e36681c2e75d/lean/Erdos9796Proof/P97/IsoscelesCount.lean#L192-L200

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
# Nine-point total isosceles count lower bound from one excess apex

In a nine-point configuration with four equidistant neighbors at every
vertex, one vertex contributing at least seven isosceles pairs forces the
total isosceles count to be at least `55`.

The statement is rehosted from
`Erdos9796Proof.P97.IsoscelesCount` at source commit
`bd8528ea10a12da2c84a10cc5897e36681c2e75d`.

The counting method is attributed to Dumitrescu (2006); the Lean
formalization is by Adam McKenna.
-/

theorem Problem97.fifty_five_le_iCount_of_card_nine_K4_of_iCountAt_ge_seven
    {A : Finset ℝ²} (hcard : A.card = 9) (hK4 : HasNEquidistantProperty 4 A)
    {p : ℝ²} (hpA : p ∈ A) (hpExtra : 7 ≤ iCountAt A p) :
    55 ≤ iCount A := by sorry
