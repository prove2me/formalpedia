-- Prove2me | Theorems.Thm_Problem97_fifty_five_le_iCount_of_card_nine_K4_of_four_class_and_extra_pair
-- name    : Problem97.fifty_five_le_iCount_of_card_nine_K4_of_four_class_and_extra_pair
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-13T03:18:24.824557+00:00
-- url     : https://prove2.me/theorems/c253f96d-013f-4517-9b37-d5cabef6b940
-- title:
--   A four-point class and extra pair outside it give the fifty-five total-count bound at nine points
-- statement:
--   If A has nine points, every point has four equidistant witnesses, and one apex has a four-point equidistant class plus an equal-distance pair with a designated endpoint outside that class, then the total isosceles count of A is at least fifty-five.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/bd8528ea10a12da2c84a10cc5897e36681c2e75d/lean/Erdos9796Proof/P97/IsoscelesCount.lean#L220-L235

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
# Nine-point count from a four-class and an extra pair

In a nine-point configuration with four equidistant neighbors at every
vertex, a four-point equidistant class and one additional equal-distance pair
at a chosen apex force the total isosceles count to be at least `55`.

The statement is rehosted from `Erdos9796Proof.P97.IsoscelesCount` at source
commit `bd8528ea10a12da2c84a10cc5897e36681c2e75d`.

The counting method is attributed to Adrian Dumitrescu (2006); the Lean
formalization is by Adam McKenna.
-/

theorem Problem97.fifty_five_le_iCount_of_card_nine_K4_of_four_class_and_extra_pair
    {A : Finset ℝ²}
    (hcard : A.card = 9) (hK4 : HasNEquidistantProperty 4 A)
    {p u v : ℝ²} (hpA : p ∈ A) {T : Finset ℝ²}
    (hTcard : 4 ≤ T.card)
    (hTsub : T ⊆ A.erase p)
    (hTdist : ∃ r : ℝ, ∀ q ∈ T, dist p q = r)
    (hpair_sub : ({u, v} : Finset ℝ²) ⊆ A.erase p)
    (hpair_card : ({u, v} : Finset ℝ²).card = 2)
    (hpair_dist : ∃ r : ℝ, ∀ q ∈ ({u, v} : Finset ℝ²), dist p q = r)
    (hu_not_mem_T : u ∉ T) :
    55 ≤ iCount A := by sorry
