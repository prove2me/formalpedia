-- Prove2me | Theorems.Thm_Problem97_boundary_card_ge_three_of_K4
-- name    : Problem97.boundary_card_ge_three_of_K4
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-13T00:51:42.826489+00:00
-- url     : https://prove2.me/theorems/e269deb3-9a3d-4148-a398-bb2efec62766
-- title:
--   The minimum enclosing circle has at least three boundary points
-- statement:
--   For a nonempty finite planar set in strictly convex position with four equidistant witnesses at every point, at least three points of the set lie on the boundary of its minimum enclosing circle.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/0c0bcc832c5070809e6010993f7c4e518523fc31/lean/Erdos9796Proof/P97/Counting.lean#L57-L63

/- Generated theorem stub from Erdos9796Proof.P97.Counting; source commit 0c0bcc832c5070809e6010993f7c4e518523fc31. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Theorems.Thm_Problem97_MEC_no_diameter_under_k4

open Problem97

/-!
# The minimum enclosing circle has at least three boundary points

`Problem97.boundary_card_ge_three_of_K4` combines non-collinearity with the
minimum-enclosing-circle diameter obstruction. Thus a nonempty strictly convex
finite planar set with four equidistant witnesses at every point has at least
three points on its minimum-enclosing-circle boundary.

Source: `Erdos9796Proof.P97.Counting`, lines 57–63, commit
`0c0bcc832c5070809e6010993f7c4e518523fc31`.
-/

open scoped EuclideanGeometry

theorem Problem97.boundary_card_ge_three_of_K4 {A : Finset ℝ²} (hne : A.Nonempty)
    (hconv : ConvexIndep A) (hK4 : HasNEquidistantProperty 4 A) :
    3 ≤ (A.filter (fun p =>
      dist p (Problem97.MEC.mec A hne).center = (Problem97.MEC.mec A hne).radius)).card := by sorry
