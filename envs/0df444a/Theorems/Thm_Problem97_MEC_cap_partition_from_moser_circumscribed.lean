-- Prove2me | Theorems.Thm_Problem97_MEC_cap_partition_from_moser_circumscribed
-- name    : Problem97.MEC.cap_partition_from_moser_circumscribed
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:50:47.446567+00:00
-- url     : https://prove2.me/theorems/29d23db4-f697-4ffe-ba2a-74df3a1dbd70
-- title:
--   Construct the Three-Cap Partition in the Circumscribed MEC Branch
-- statement:
--   Let A be a nonempty noncollinear finite planar set, and let a Moser triangle for A lie in the circumscribed minimum-enclosing-circle branch. Assume its signed area is nonzero and every other vertex of A belongs to exactly one of the three algebraically defined opposite arcs. Then the triangle determines a cap triple over A with the required strengthened arc-membership data.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_MEC_cap_partition_from_moser_circumscribed.lean#L1-L180

/- Generated theorem stub from Erdos9796Proof.P97.Cap.PartitionFromMEC by Stage 2 proof cut; source SHA-256 cb2a5ce1101a74572ab57000424dc5f4df662f147fba1a7de73bfcf938646f93 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Cap_PartitionFromMEC
import Definitions.Def_Erdos9796Counting_Cap_Structure
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Definitions.Def_Erdos9796Counting_Moser_Triangle
open Problem97 Problem97.MEC



/-!
# Cap partition from a circumscribed Moser triangle

This file bridges the geometric `Problem97.MEC.MoserTriangle`
(produced by the Sylvester dichotomy) to the structural
`Problem97.MoserTriangle` and from there to a `Problem97.CapTriple`
with the strengthened `arc_membership` field.

We restrict to the **circumscribed branch** of the dichotomy
(`case_split = Or.inl _`), where the three MEC-boundary vertices are
pairwise distinct.  The diameter branch (`Or.inr _`) is not handled
here; downstream consumers branch on the dichotomy.

The cap construction is the natural closed-arc filter using the
chord-separation predicate `Problem97.OnArcOpposite`:
* `C1 := A.filter (fun v => OnArcOpposite v1 v2 v3 v)`
* `C2 := A.filter (fun v => OnArcOpposite v2 v3 v1 v)`
* `C3 := A.filter (fun v => OnArcOpposite v3 v1 v2 v)`

Moser-vertex memberships fall out of algebraic identities (e.g.
`signedArea2 v1 v3 v1 = 0`) and the noncollinearity of the Moser
triangle vertices.  The "opposite apex not in own cap" clauses
(`v1 ∉ C1`, etc.) use that `signedArea2 v1 v2 v3 ≠ 0`.

## The `hAGenericCapCount` hypothesis

The closed-cap convention via `OnArcOpposite` is *algebraic* and does
not by itself imply that every non-Moser `A`-vertex lies in exactly
one cap.  Geometric counterexamples (e.g. a point strictly inside the
Moser triangle gives `0` caps; a point in a corner region gives `2`
caps) show the count is in `{0, 1, 2, 3}` over the affine plane.  For
the closed-cap-partition identity `|C1| + |C2| + |C3| = |A| + 3` to
hold downstream, we need the count to be exactly `1` on non-Moser
vertices — a *geometric* fact about A-vertices being either on the
MEC arc opposite to one of the Moser vertices, or strictly outside
exactly one chord.

We expose this as an explicit hypothesis `hAGenericCapCount`, which
downstream consumers establish via MEC + ConvexIndep + circumscribed
case structure.

## Main declarations

* Algebraic identities for `signedArea2` (`signedArea2_self_*`).
* Lemmas `onArcOpposite_of_chord_endpoint_{left,right}` — Moser
  vertex endpoints lie on their adjacent caps.
* `Problem97.signedArea2_eq_zero_of_onArcOpposite_self` — apex lies
  on its own cap only if the area degenerates.
* `Problem97.MEC.MoserTriangle.toStructural` — project the
  circumscribed branch to a structural `Problem97.MoserTriangle`.
* `Problem97.MEC.cap_partition_from_moser_circumscribed` — the main
  cap-partition existence theorem.
* `Problem97.SurplusCapPacket` — Moser triangle (carried as a
  non-obtuse circumscribed MEC triangle plus the circumscribed
  case-split) + cap triple over its structural projection +
  designation of one cap as surplus (`|Ci| > 4`).  This is the
  MEC-aware packet that downstream U1 sub-lemmas consume.
* `Problem97.SurplusCapPacket.IsM44` — predicate saying the cap
  multiset is `(m, 4, 4)` with `m ≥ 5`, and the surplus cap is the
  long one.
-/

open scoped EuclideanGeometry
open Finset



/- ### Algebraic identities for `signedArea2` -/





/- ### `OnArcOpposite` for Moser vertices -/









/- ### Bridge: circumscribed `MEC.MoserTriangle` → structural `MoserTriangle` -/



/- ### Cap-partition existence theorem -/

open Classical in

theorem Problem97.MEC.cap_partition_from_moser_circumscribed
    {A : Finset ℝ²} {hA : A.Nonempty} {hncol : ¬ Collinear ℝ (A : Set ℝ²)}
    (MT : Problem97.MEC.MoserTriangle A hA hncol)
    (hCircumscribed : ∃ h12 h23 h13,
      MT.case_split = Or.inl ⟨h12, h23, h13⟩)
    (hMoserNonDeg : Problem97.signedArea2 MT.v1 MT.v2 MT.v3 ≠ 0)
    (hAGenericCapCount : ∀ v ∈ A, v ≠ MT.v1 → v ≠ MT.v2 → v ≠ MT.v3 →
      (if Problem97.OnArcOpposite MT.v1 MT.v2 MT.v3 v then 1 else 0)
        + (if Problem97.OnArcOpposite MT.v2 MT.v3 MT.v1 v then 1 else 0)
        + (if Problem97.OnArcOpposite MT.v3 MT.v1 MT.v2 v then 1 else 0)
        = 1) :
    Nonempty (Problem97.CapTriple A (MT.toStructural hCircumscribed)) := by sorry
