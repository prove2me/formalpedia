-- Prove2me | Theorems.Thm_Problem97_not_collinear_of_K4
-- name    : Problem97.not_collinear_of_K4
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-13T00:21:36.978696+00:00
-- url     : https://prove2.me/theorems/88c2841e-ba46-4e4f-940b-f911321baba5
-- title:
--   Four equidistant witnesses and strict convexity rule out collinearity
-- statement:
--   A nonempty finite planar set in strictly convex position, with four equidistant witnesses at every point, is not collinear.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/0c0bcc832c5070809e6010993f7c4e518523fc31/lean/Erdos9796Proof/P97/Counting.lean#L47-L52

/- Generated theorem stub from Erdos9796Proof.P97.Counting; source commit 0c0bcc832c5070809e6010993f7c4e518523fc31. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Theorems.Thm_Problem97_card_ge_five_of_K4
import Theorems.Thm_Problem97_ConvexIndep_not_collinear_of_card_ge_three

open Problem97

/-!
# Four equidistant witnesses and strict convexity rule out collinearity

`Problem97.not_collinear_of_K4` packages the lower bound of five points with
the strict-convexity obstruction for sets of cardinality at least three.

Source: `Erdos9796Proof.P97.Counting`, lines 47–52, commit
`0c0bcc832c5070809e6010993f7c4e518523fc31`.
-/

open scoped EuclideanGeometry

theorem Problem97.not_collinear_of_K4 {A : Finset ℝ²} (hne : A.Nonempty)
    (hconv : ConvexIndep A) (hK4 : HasNEquidistantProperty 4 A) :
    ¬ Collinear ℝ (A : Set ℝ²) := by sorry
