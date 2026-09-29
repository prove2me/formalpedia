-- Prove2me | Theorems.Thm_Problem97_CGN_CGN4g_strictCapBlockData_of_supportCap_oriented
-- name    : Problem97.CGN.CGN4g_strictCapBlockData_of_supportCap_oriented
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T05:47:14.877699+00:00
-- url     : https://prove2.me/theorems/6754eebd-7705-4568-b14e-810f23fe6966
-- title:
--   Package an Oriented Support Cap as Strict Cap-Block Data
-- statement:
--   Given a convex-independent set, an oriented support-cap description from a nonobtuse Moser triangle, and a circumscribed MEC packet, there is strict cap-block data whose ordered endpoints are the two specified cap vertices in one of the two possible orientations.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/14bcb9baa1b2ce2dd563e5a43527a30b7582483f/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_CGN_CGN4g_strictCapBlockData_of_supportCap_oriented.lean#L1-L125

/- Generated theorem stub from Erdos9796Proof.P97.CGN.CGN4g by Stage 2 proof cut; source SHA-256 c412b95ca627805e0db3a1f0d192f80b93891249e4eb1369844d4f8206dcba79 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_CGN_CGN4g
import Definitions.Def_Erdos9796Counting_Cap_Structure
import Definitions.Def_Erdos9796Counting_CircumscribedMECPacket
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
open Problem97 Problem97.CGN



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

theorem Problem97.CGN.CGN4g_strictCapBlockData_of_supportCap_oriented
    {A C : Finset ℝ²} {M : Problem97.MoserTriangle A}
    (hA : Problem97.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²))
    (hC_subset : C ⊆ A)
    (hC_arc : ∀ x ∈ A, x ∈ C ↔ Problem97.OnArcOpposite M.v1 M.v2 M.v3 x)
    (hv_mem : M.v2 ∈ C)
    (hw_mem : M.v3 ∈ C)
    (P : Problem97.CircumscribedMECPacket A M)
    (hacute : 0 ≤ ⟪M.v2 - M.v1, M.v3 - M.v1⟫_ℝ) :
    ∃ B : StrictCapBlockData A C,
      (B.L.points (firstIndex B.Packet.hm) = M.v2 ∧
          B.L.points (lastIndex B.Packet.hm) = M.v3) ∨
        (B.L.points (firstIndex B.Packet.hm) = M.v3 ∧
          B.L.points (lastIndex B.Packet.hm) = M.v2) := by sorry
