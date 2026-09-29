-- Prove2me | Theorems.Thm_Problem97_CGN_CGN6d0_positiveSideBisector_to_wbtw
-- name    : Problem97.CGN.CGN6d0_positiveSideBisector_to_wbtw
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T02:14:49.318954+00:00
-- url     : https://prove2.me/theorems/3793007d-55e6-4abc-8cc7-69b25b3ae15d
-- title:
--   Same-Side Bisector Apices Give Midpoint Betweenness
-- statement:
--   If x and y are distinct and two apices a and b are equidistant from x and y and lie on the same positive side of the perpendicular bisector, then the midpoint of x and y is weakly between a and b in one of the two endpoint orders.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_CGN_CGN6d0_positiveSideBisector_to_wbtw.lean#L1-L145

/- Generated theorem stub from Erdos9796Proof.P97.CGN.CGN6 by Stage 2 proof cut; source SHA-256 87eeea2860c10b6c484c3d7aec9f295605a553c9956e5cc04bbc649402bc9c30 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Order.Interval.Finset.Fin
open Problem97 Problem97.CGN



/-!
# CGN6: normalized minor-cap chain model

This file starts the CGN6 layer named in the updated counterexample-card-ge-nine
prose. It records the normalized minor-cap chain data the prose uses for the
CGN6b slope-product argument: ordered coordinates, endpoint normalization, the
unit-disk bound, and the adjacent-slope bookkeeping.

The actual geometric construction of this model from a concrete MEC cap packet
is still separate. This file only provides the data interface the subsequent
CGN6b / CGN6c proofs will consume.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped BigOperators


























/- ### CGN6norm scaffold

The prose normalization theorem uses an explicit coordinate frame
centered at the chord midpoint and aligned with the chord / inward
normal directions.  The full packet-to-frame bridge is still separate;
this helper records the coordinate map in the exact algebraic form used
by the prose.
-/































-- The normalization proof is large enough to need a higher elaboration budget.

theorem Problem97.CGN.CGN6d0_positiveSideBisector_to_wbtw
    {x y a b : ℝ²}
    (hx : x ≠ y)
    (haeq : dist a x = dist a y)
    (hbeq : dist b x = dist b y)
    (ha_pos : 0 < signedArea2 x y a)
    (hb_pos : 0 < signedArea2 x y b) :
    Wbtw ℝ (midpoint ℝ x y) a b ∨ Wbtw ℝ (midpoint ℝ x y) b a := by sorry
