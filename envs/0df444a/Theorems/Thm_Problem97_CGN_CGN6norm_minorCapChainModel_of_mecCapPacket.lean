-- Prove2me | Theorems.Thm_Problem97_CGN_CGN6norm_minorCapChainModel_of_mecCapPacket
-- name    : Problem97.CGN.CGN6norm_minorCapChainModel_of_mecCapPacket
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:44:44.563709+00:00
-- url     : https://prove2.me/theorems/40bfbbcc-e9b1-4778-901d-67f9d8ec79d4
-- title:
--   Normalize an MEC Cap Packet to a Minor-Cap Chain Model
-- statement:
--   Given an ordered cap with a minimum-enclosing-circle packet, the prescribed minor-cap side conditions, and strict cap order, there exists an injective plane transformation T with similarity-transport data such that the transformed ordered cap supports a minor-cap chain model.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_CGN_CGN6norm_minorCapChainModel_of_mecCapPacket.lean#L1-L147

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
set_option maxHeartbeats 600000 in

theorem Problem97.CGN.CGN6norm_minorCapChainModel_of_mecCapPacket
    {A : Finset ℝ²} {m : ℕ} {L : OrderedCap m}
    (Packet : MecCapPacket A L)
    (Hside : MinorCapSideHypotheses Packet)
    (Hord : StrictCapOrder A L) :
    ∃ T, ∃ hT : Function.Injective T, ∃ tau : SimilarityTransportData T,
      Nonempty (MinorCapChainModel (L.map T hT)) := by sorry
