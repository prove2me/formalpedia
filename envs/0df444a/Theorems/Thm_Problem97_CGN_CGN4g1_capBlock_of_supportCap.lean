-- Prove2me | Theorems.Thm_Problem97_CGN_CGN4g1_capBlock_of_supportCap
-- name    : Problem97.CGN.CGN4g1_capBlock_of_supportCap
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:42:38.160142+00:00
-- url     : https://prove2.me/theorems/acb4d509-e420-4aa8-b376-84ceac661da1
-- title:
--   Package a Support Cap as an Ordered MEC Boundary Block
-- statement:
--   Let an injective enumeration φ of a finite planar set A identify a support cap C with the closed index interval from lo to hi. Assume C lies in a disk with center c and nonnegative radius r, both interval endpoints lie on the boundary circle, C lies on the nonnegative side of the endpoint chord, and c lies on its nonpositive side. Then C admits an ordered-cap representation, an associated minimum-enclosing-circle packet and side hypotheses, and a boundary-block structure whose endpoints are lo and hi.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_CGN_CGN4g1_capBlock_of_supportCap.lean#L1-L129

/- Generated theorem stub from Erdos9796Proof.P97.CGN.CGN4g by Stage 2 proof cut; source SHA-256 c412b95ca627805e0db3a1f0d192f80b93891249e4eb1369844d4f8206dcba79 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_CGN_CGN4g
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

theorem Problem97.CGN.CGN4g1_capBlock_of_supportCap
    {A C : Finset ℝ²} {n : ℕ} {phi : Fin n → ℝ²}
    (hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    {lo hi : Fin n} (hlohi : lo < hi)
    (hC_interval : ∀ x : ℝ²,
      x ∈ C ↔ ∃ q : Fin n, lo ≤ q ∧ q ≤ hi ∧ phi q = x)
    (center : ℝ²) (radius : ℝ)
    (hradius_nonneg : 0 ≤ radius)
    (hdisk_C : ∀ x, x ∈ C → dist x center ≤ radius)
    (hlo_circle : dist (phi lo) center = radius)
    (hhi_circle : dist (phi hi) center = radius)
    (hcap_side : ∀ x, x ∈ C ->
      0 ≤ Problem97.signedArea2 (phi lo) (phi hi) x)
    (hcenter_side :
      Problem97.signedArea2 (phi lo) (phi hi) center ≤ 0) :
    ∃ m, ∃ L : OrderedCap m,
      ∃ Packet : MecCapPacket A L,
      ∃ _Hside : MinorCapSideHypotheses Packet,
      ∃ _Block : BoundaryCapBlock A C phi L,
        _Block.lo = lo ∧ _Block.hi = hi := by sorry
