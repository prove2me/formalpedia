-- Prove2me | Theorems.Thm_Problem97_K4_delete_of_indeg_zero
-- name    : Problem97.K4_delete_of_indeg_zero
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-13T02:20:44.162894+00:00
-- url     : https://prove2.me/theorems/96b559b8-b5db-46e4-8dff-3e9a0c79941a
-- title:
--   Deleting an unused witness point preserves four equidistant neighbours
-- statement:
--   Let A be a nonempty finite planar set in strictly convex position with four equidistant neighbours at every point, and let S be a witness system. If x belongs to A and to none of the selected witness classes, then deleting x leaves a nonempty strictly convex set in which every point still has four equidistant neighbours.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/387e5b44ae26906725a4898b0a01c2d7345ddb38/lean/Erdos9796Proof/P97/K4WitnessDeletion.lean#L43-L67

/- Rehosted from Erdos9796Proof.P97.K4WitnessDeletion at source commit
   387e5b44ae26906725a4898b0a01c2d7345ddb38. -/
import Definitions.Def_Problem97_IsWitnessSystem
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation

open scoped EuclideanGeometry
open Finset

open Problem97

theorem Problem97.K4_delete_of_indeg_zero {A : Finset ℝ²} (hne : A.Nonempty)
    (hconv : ConvexIndep A) (hK4 : HasNEquidistantProperty 4 A)
    {S : ℝ² → Finset ℝ²} (hS : IsWitnessSystem A S)
    {x : ℝ²} (hxA : x ∈ A) (hindeg0 : ∀ y ∈ A, x ∉ S y) :
    (A.erase x).Nonempty ∧ ConvexIndep (A.erase x) ∧
      HasNEquidistantProperty 4 (A.erase x) := by sorry
