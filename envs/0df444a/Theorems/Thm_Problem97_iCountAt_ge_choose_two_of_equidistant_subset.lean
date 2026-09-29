-- Prove2me | Theorems.Thm_Problem97_iCountAt_ge_choose_two_of_equidistant_subset
-- name    : Problem97.iCountAt_ge_choose_two_of_equidistant_subset
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-13T03:16:27.087545+00:00
-- url     : https://prove2.me/theorems/1c1637cf-e77a-4d15-932b-86452c22ccb6
-- title:
--   Equidistant neighbours give one local pair per unordered pair
-- statement:
--   If S is a finite set of points in A.erase p at one common distance from p, then the number of two-element subsets of S is at most the isosceles count at p.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/bd8528ea10a12da2c84a10cc5897e36681c2e75d/lean/Erdos9796Proof/P97/IsoscelesCount.lean#L58-L68

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
# Local isosceles count from an equidistant subset

Every unordered pair in an equidistant set of neighbors gives an isosceles
pair at the common apex, so the local count is at least `choose(S.card, 2)`.

The statement is rehosted from
`Erdos9796Proof.P97.IsoscelesCount` at source commit
`bd8528ea10a12da2c84a10cc5897e36681c2e75d`.

The counting method is attributed to Adrian Dumitrescu (2006); the Lean
formalization is by Adam McKenna.
-/

theorem Problem97.iCountAt_ge_choose_two_of_equidistant_subset
    (A : Finset ℝ²) (p : ℝ²) (S : Finset ℝ²)
    (hSsub : S ⊆ A.erase p)
    (hSdist : ∃ r : ℝ, ∀ q ∈ S, dist p q = r) :
    S.card.choose 2 ≤ iCountAt A p := by sorry
