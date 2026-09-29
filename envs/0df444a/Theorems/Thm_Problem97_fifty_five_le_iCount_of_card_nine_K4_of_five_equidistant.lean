-- Prove2me | Theorems.Thm_Problem97_fifty_five_le_iCount_of_card_nine_K4_of_five_equidistant
-- name    : Problem97.fifty_five_le_iCount_of_card_nine_K4_of_five_equidistant
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-13T03:17:50.378976+00:00
-- url     : https://prove2.me/theorems/27ae9d05-173b-4e57-90f9-fa3df15c17d2
-- title:
--   Five equidistant neighbours give the fifty-five total-count bound at nine points
-- statement:
--   If A has nine points, every point has four equidistant witnesses, and one apex has at least five equidistant neighbours at one radius, then the total isosceles count of A is at least fifty-five.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/bd8528ea10a12da2c84a10cc5897e36681c2e75d/lean/Erdos9796Proof/P97/IsoscelesCount.lean#L205-L218

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
# Fifty-five total isosceles pairs from the five-equidistant shape

In a nine-point configuration with four equidistant neighbors at every
vertex, five equidistant neighbors at one apex force the total isosceles
count to be at least `55`.

The statement is rehosted from
`Erdos9796Proof.P97.IsoscelesCount` at source commit
`bd8528ea10a12da2c84a10cc5897e36681c2e75d`.

The counting method is attributed to Adrian Dumitrescu (2006); the Lean
formalization is by Adam McKenna.
-/

theorem Problem97.fifty_five_le_iCount_of_card_nine_K4_of_five_equidistant
    {A : Finset ℝ²}
    (hcard : A.card = 9) (hK4 : HasNEquidistantProperty 4 A)
    {p : ℝ²} (hpA : p ∈ A) {S : Finset ℝ²}
    (hScard : 5 ≤ S.card)
    (hSsub : S ⊆ A.erase p)
    (hSdist : ∃ r : ℝ, ∀ q ∈ S, dist p q = r) :
    55 ≤ iCount A := by sorry
