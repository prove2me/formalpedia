-- Prove2me | Theorems.Thm_Problem97_CGN_CGN6c_oneSidedDistanceInjective
-- name    : Problem97.CGN.CGN6c_oneSidedDistanceInjective
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T02:14:30.105904+00:00
-- url     : https://prove2.me/theorems/186f528b-af9b-4d80-9d62-4420edc2baa8
-- title:
--   Distances from One Cap Vertex Are One-Sided Injective
-- statement:
--   For a minor-cap chain model, a fixed chain vertex has distinct distances to later chain vertices, and also distinct distances to earlier chain vertices.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_CGN_CGN6c_oneSidedDistanceInjective.lean#L1-L145

/- Generated theorem stub from Erdos9796Proof.P97.CGN.CGN6 by Stage 2 proof cut; source SHA-256 87eeea2860c10b6c484c3d7aec9f295605a553c9956e5cc04bbc649402bc9c30 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_CGN_CGN6
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

theorem Problem97.CGN.CGN6c_oneSidedDistanceInjective {m : ℕ} {L : OrderedCap m}
    (M : MinorCapChainModel L) :
    (∀ {j r s : Fin m}, j < r → r < s →
      dist (L.points j) (L.points r) ≠ dist (L.points j) (L.points s)) ∧
    (∀ {j r s : Fin m}, r < s → s < j →
      dist (L.points j) (L.points r) ≠ dist (L.points j) (L.points s)) := by sorry
