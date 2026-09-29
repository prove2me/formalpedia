-- Prove2me | Theorems.Thm_Problem97_CGN_CGN6b0_secantEndpointBounds_coords
-- name    : Problem97.CGN.CGN6b0_secantEndpointBounds_coords
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T02:02:21.602156+00:00
-- url     : https://prove2.me/theorems/7b424c0b-c093-4c82-ac3d-270bf9ff9fc7
-- title:
--   Endpoint secant bounds for a normalized minor-cap chain
-- statement:
--   Let a normalized minor-cap chain have indexed coordinates $(X_i,Y_i)$ and decreasing adjacent slopes. For $0<i<j<m$, the secant slope from $i$ to $j$ is at most the secant slope from the first endpoint to $j$; for $j<k<m$, the secant slope from $j$ to $k$ is at least the secant slope from $j$ to the last endpoint. These inequalities are the coordinate core of the cap-angle argument.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_CGN_CGN6b0_secantEndpointBounds_coords.lean#L1-L144

/- Generated theorem stub from Erdos9796Proof.P97.CGN.CGN6 by Stage 2 proof cut; source SHA-256 87eeea2860c10b6c484c3d7aec9f295605a553c9956e5cc04bbc649402bc9c30 -/
import Definitions.Def_Erdos9796Counting_Adapter
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

theorem Problem97.CGN.CGN6b0_secantEndpointBounds_coords {m : ℕ} (L : MinorCapChainCoords m) :
    (∀ {i j : ℕ} (hi : 0 < i) (hij : i < j) (hj : j < m),
      slopeAt L.X L.Y i j (by omega) hj ≤ slopeAt L.X L.Y 0 j (by omega) hj) ∧
    (∀ {j k : ℕ} (hjk : j < k) (hk : k < m),
      slopeAt L.X L.Y j k (by omega) (by omega) ≥
        slopeAt L.X L.Y j (m - 1) (by omega) (by omega)) := by sorry
