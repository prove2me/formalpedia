-- Prove2me | Theorems.Thm_Problem97_boundaryCap_chordProjection_strict
-- name    : Problem97.boundaryCap_chordProjection_strict
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:43:45.552845+00:00
-- url     : https://prove2.me/theorems/0a843193-285f-4d76-865c-53542313e1b4
-- title:
--   Strict Chord-Projection Order Along a Boundary Cap
-- statement:
--   For a convex-independent finite planar set, let L be a boundary cap block whose global enumeration has strictly negative signed area on increasing triples. If L carries a minimum-enclosing-circle packet with the cap and center on opposite closed sides of its endpoint chord, then whenever r < s, the displacement from L(r) to L(s) has strictly positive inner product with the oriented endpoint chord. Thus chord projection strictly increases along the cap order.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_boundaryCap_chordProjection_strict.lean#L1-L124

/- Generated theorem stub from Erdos9796Proof.P97.CGN.CGN4g by Stage 2 proof cut; source SHA-256 c412b95ca627805e0db3a1f0d192f80b93891249e4eb1369844d4f8206dcba79 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_CGN_CGN4g
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
open Problem97



/-!
# CGN4g: ordered-cap block packaging

This file adds the closure-plan data carrier for the ordered-cap block cut out
of a global convex-boundary enumeration, together with the theorem wrappers
that are pure packaging.

The geometric producers for the block (`CGN4g1`, `CGN4g3`, `CGN4g4`) remain
separate. The declarations here are the sanctioned interfaces consumed by the
existing CGN6 / CGN7 layers.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace












variable {A C : Finset ℝ²}















































set_option maxHeartbeats 2000000 in
-- The boundary-cap projection normalization expands several basis-coordinate
-- identities and signed-area formulas in one theorem.

theorem Problem97.boundaryCap_chordProjection_strict
    {A C : Finset ℝ²} {n m : ℕ}
    {phi : Fin n → ℝ²} {L : Problem97.CGN.OrderedCap m}
    (_hA : Problem97.ConvexIndep A)
    (Block : Problem97.CGN.BoundaryCapBlock A C phi L)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi i) (phi j) (phi k) < 0)
    (Packet : Problem97.CGN.MecCapPacket A L)
    (Hside : Problem97.CGN.MinorCapSideHypotheses Packet) :
    ∀ {r s : Fin m}, r < s ->
      0 < inner ℝ (L.points s - L.points r)
        (L.points (Problem97.CGN.lastIndex Packet.hm) -
          L.points (Problem97.CGN.firstIndex Packet.hm)) := by sorry
