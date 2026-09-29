-- Prove2me | Theorems.Thm_Problem97_CGN8_circumscribed_iCount_upper_bound
-- name    : Problem97.CGN8_circumscribed_iCount_upper_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T05:47:55.885144+00:00
-- url     : https://prove2.me/theorems/9be630a2-d863-419b-a33d-d561cc147450
-- title:
--   Circumscribed Caps Bound the Isosceles Count
-- statement:
--   For a nonempty noncollinear convex-independent finite planar set with at least three MEC-boundary points, the total isosceles count satisfies iCount A ≤ ((11 · |A|² − 18 · |A|) / 12) over ℝ.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/14bcb9baa1b2ce2dd563e5a43527a30b7582483f/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_CGN8_circumscribed_iCount_upper_bound.lean#L1-L42

/- Generated theorem stub from Erdos9796Proof.P97.CGN.CGN8 by Stage 2 proof cut; source SHA-256 e0d08238ab808e6b673b9006abffb488ad895fb6cf431ea389289a83884af65d -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open Problem97



/-!
# CGN8: circumscribed cap upper bound

This module is the circumscribed-branch counting closure from the
counterexample-card-ge-nine prose. It combines the three-cap decomposition,
the CGN4g support-cap packaging, the CGN6/CGN7 cap-local saving, the
intra-cap disjointness lemma, and the cap-size Cauchy-Schwarz bound to
produce the final circumscribed upper bound on `iCount`.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped BigOperators
open Finset



set_option maxHeartbeats 600000 in
-- CGN8 packages three cap extractions, three cap-local savings, and the final
-- finset/cardinality arithmetic in one theorem; elaboration needs a higher cap.

theorem Problem97.CGN8_circumscribed_iCount_upper_bound
    {A : Finset ℝ²}
    (hne : A.Nonempty)
    (hnoncol : ¬ Collinear ℝ (A : Set ℝ²))
    (hconv : ConvexIndep A)
    (hbd : 3 <= (A.filter (fun p =>
      dist p (Problem97.MEC.mec A hne).center =
        (Problem97.MEC.mec A hne).radius)).card) :
    (iCount A : ℝ) <= ((11 : ℝ) * A.card ^ 2 - 18 * A.card) / 12 := by sorry
