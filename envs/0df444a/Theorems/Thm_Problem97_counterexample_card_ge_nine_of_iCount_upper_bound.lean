-- Prove2me | Theorems.Thm_Problem97_counterexample_card_ge_nine_of_iCount_upper_bound
-- name    : Problem97.counterexample_card_ge_nine_of_iCount_upper_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-13T01:02:46.648059+00:00
-- url     : https://prove2.me/theorems/f1142dad-239d-4015-b1cb-78fdd145b1ae
-- title:
--   The isosceles-count upper bound forces at least nine points
-- statement:
--   Let A be a nonempty finite planar set in strictly convex position with four equidistant witnesses at every point. If its total isosceles count is at most (11|A|² - 18|A|)/12, then A has at least nine points.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/0c0bcc832c5070809e6010993f7c4e518523fc31/lean/Erdos9796Proof/P97/Counting.lean#L73-L86

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Author: Adam McKenna
-/

import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Theorems.Thm_Problem97_card_ge_five_of_K4
import Theorems.Thm_Problem97_counting_arithmetic

open scoped EuclideanGeometry
open Finset
open Problem97

/-!
# Conditional counting assembly for the nine-point lower bound

This theorem combines the `6 * A.card ≤ iCount A` lower bound with the
quadratic upper bound supplied as a hypothesis. The count convention follows
Dumitrescu's isosceles-count method; that attribution records the source of
the counting strategy and does not assert the upper bound here.
-/

theorem Problem97.counterexample_card_ge_nine_of_iCount_upper_bound
    {A : Finset ℝ²} (hne : A.Nonempty) (_hconv : ConvexIndep A)
    (hK4 : HasNEquidistantProperty 4 A)
    (hup : (iCount A : ℝ) ≤ ((11 : ℝ) * A.card ^ 2 - 18 * A.card) / 12) :
    9 ≤ A.card := by
  sorry
