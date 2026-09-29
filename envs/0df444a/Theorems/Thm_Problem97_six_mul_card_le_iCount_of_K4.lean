-- Prove2me | Theorems.Thm_Problem97_six_mul_card_le_iCount_of_K4
-- name    : Problem97.six_mul_card_le_iCount_of_K4
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-13T00:09:01.54932+00:00
-- url     : https://prove2.me/theorems/28b441f6-e78c-4f83-89d6-cdaa9c0c5065
-- title:
--   Four equidistant witnesses give six isosceles pairs per vertex
-- statement:
--   If every point of a finite planar set has four points of the set at one common positive distance, then six times the number of points is at most the total isosceles count of the set.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/bd8528ea10a12da2c84a10cc5897e36681c2e75d/lean/Erdos9796Proof/P97/IsoscelesCount.lean#L153-L162

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Author: Adam McKenna <adam@mysticflounder.ai>
-/

import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Theorems.Thm_Problem97_iCountAt_ge_six_of_K4

open scoped EuclideanGeometry
open Problem97

/-!
# Total isosceles count lower bound under the four-equidistant property

This is the Dumitrescu counting lower bound: four equidistant neighbors at
each vertex force six isosceles pairs at that vertex, and summing over the
vertices gives `6 * A.card ≤ iCount A`. The counting convention is the one
used by Dumitrescu (2006), with equilateral triangles counted three times.

The statement is rehosted from
`Erdos9796Proof.P97.IsoscelesCount` at source commit
`bd8528ea10a12da2c84a10cc5897e36681c2e75d`.
-/

theorem Problem97.six_mul_card_le_iCount_of_K4 {A : Finset ℝ²}
    (hK4 : HasNEquidistantProperty 4 A) : 6 * A.card ≤ iCount A := by sorry
