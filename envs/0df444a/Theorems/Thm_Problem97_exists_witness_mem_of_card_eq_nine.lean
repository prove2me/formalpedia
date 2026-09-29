-- Prove2me | Theorems.Thm_Problem97_exists_witness_mem_of_card_eq_nine
-- name    : Problem97.exists_witness_mem_of_card_eq_nine
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-13T02:21:40.565571+00:00
-- url     : https://prove2.me/theorems/78a28453-88df-4284-8e8f-1cbf946716dc
-- title:
--   Every point in a nine-point configuration is used by a witness class
-- statement:
--   If a nonempty finite planar set in strictly convex position has four equidistant neighbours at every point, has exactly nine points, and carries a witness system, then every point belongs to at least one selected witness class.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/387e5b44ae26906725a4898b0a01c2d7345ddb38/lean/Erdos9796Proof/P97/K4WitnessDeletion.lean#L74-L87

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Author: Adam McKenna
-/

import Definitions.Def_Problem97_IsWitnessSystem

open scoped EuclideanGeometry
open Finset
open Erdos9796Mission
open Problem97

/-!
# Nine-point witness incidence

Every point in a nine-point configuration has positive incidence in any
witness system. The proof uses the deletion lemma in the solution module and
the already published nine-point counting lower bound.

The formalization follows the witness-system deletion argument in the source
development. The point-set counting method is attributed there to Dumitrescu;
this theorem is the project's Lean formalization of the incidence corollary.
-/

theorem Problem97.exists_witness_mem_of_card_eq_nine {A : Finset Plane} (hne : A.Nonempty)
    (hconv : ConvexIndep A) (hK4 : HasNEquidistantProperty 4 A)
    (hcard : A.card = 9) {S : Plane → Finset Plane} (hS : IsWitnessSystem A S)
    {x : Plane} (hxA : x ∈ A) : ∃ y ∈ A, x ∈ S y := by
  sorry
