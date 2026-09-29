-- Prove2me | Theorems.Thm_Problem97_MEC_arc_partition_count_eq_one
-- name    : Problem97.MEC.arc_partition_count_eq_one
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T02:10:47.774012+00:00
-- url     : https://prove2.me/theorems/4569e06a-dfe4-4906-bdbb-e959c68ace19
-- title:
--   Every Nonvertex Lies on Exactly One Opposite Arc
-- statement:
--   For a convex-independent set and a circumscribed Moser triangle, every point of the set distinct from the triangle's three vertices belongs to exactly one of the three opposite-arc predicates.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_MEC_arc_partition_count_eq_one.lean#L1-L122

/- Generated theorem stub from Erdos9796Proof.P97.ArcPartitionCount by Stage 2 proof cut; source SHA-256 572f8bf0c2c29f5db2afe9ef8dfa5a179cea8a5fabea8a5ecd5dcd76c653030d -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Definitions.Def_Erdos9796Counting_Moser_Triangle
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Hull
open Problem97 Problem97.MEC



/-!
# Arc-partition count for the MEC cap partition (Problem 97)

`Problem97.MEC.arc_partition_count_eq_one` discharges the
`hAGenericCapCount` hypothesis of
`Problem97.MEC.cap_partition_from_moser_circumscribed`.

For a convex-independent finite point set `A ⊆ ℝ²` and a Moser triangle
`{v1, v2, v3}` produced by the Sylvester dichotomy on its
circumscribed branch (the three Moser vertices are pairwise distinct
and on the MEC boundary), every non-Moser `A`-vertex lies on *exactly
one* of the three closed caps `Ci`, where each `Ci` is defined by
the `OnArcOpposite` chord-separation predicate.

## Proof outline

For each non-Moser `v ∈ A`, we use the barycentric decomposition with
base point `v3`:
`v - v3 = a (v1 - v3) + b (v2 - v3)`.
Then by an affine ring identity:
* `signedArea2 v v2 v3 = a · Δ`
* `signedArea2 v v3 v1 = b · Δ`
* `signedArea2 v v1 v2 = (1 - a - b) · Δ`
where `Δ = signedArea2 v1 v2 v3`.

Hence the three `OnArcOpposite` indicators reduce to:
* `i₁ = 1 ↔ a · Δ² ≤ 0 ↔ a ≤ 0`
* `i₂ = 1 ↔ b · Δ² ≤ 0 ↔ b ≤ 0`
* `i₃ = 1 ↔ (1 - a - b) · Δ² ≤ 0 ↔ a + b ≥ 1`

**Step 1**: Show `Δ ≠ 0` (non-degenerate triangle). If `Δ = 0`, the
three Moser vertices are collinear; the Wbtw-trichotomy + ConvexIndep
gives a contradiction.

**Step 2**: For non-Moser `v ∈ A`, show `a, b, 1-a-b` are all
non-zero (i.e., `v` is not on any chord). If, e.g., `a = 0`, then
`signedArea2 v v2 v3 = 0`, so `v, v2, v3` are collinear. Combined
with `v ∈ A`, MEC enclosing, `v2, v3` on MEC boundary, we deduce
`v ∈ segment v2 v3`. By ConvexIndep, contradiction.

**Step 3**: Rule out `a < 0 ∧ b < 0` (two-negative corner at `v3`).
Use the supporting-hyperplane argument: `v3` on the MEC boundary
means the tangent at `v3` separates the closed disk from the
"outside-the-tangent" half-plane. The corner region {a, b < 0} lies
strictly outside the tangent. So `v` in the disk cannot have both
`a, b < 0`. Symmetric arguments at `v1, v2` rule out the other two
two-negative cases.

**Step 4**: Rule out `a, b, 1-a-b` all having the same sign as `−Δ²`
— impossible since they sum to 1.

**Step 5**: Therefore exactly one indicator is 1.

## Main declarations

* `Problem97.MEC.arc_partition_count_eq_one` — the cap-count
  identity, dispatched to `hAGenericCapCount` downstream.
-/

open scoped EuclideanGeometry
open Finset Classical




/- ### Barycentric/area algebraic identities -/









/- ### Inner-product / sphere identities -/





/- ### Corner exclusion -/



/- ### Non-degeneracy of the Moser triangle under ConvexIndep -/



/- ### Chord exclusion: non-Moser A-vertex not on any chord -/



/- ### Main theorem -/

open Classical in

theorem Problem97.MEC.arc_partition_count_eq_one
    {A : Finset ℝ²} {hA : A.Nonempty} {hncol : ¬ Collinear ℝ (A : Set ℝ²)}
    (hConv : Problem97.ConvexIndep A)
    (MT : Problem97.MEC.MoserTriangle A hA hncol)
    (hCircumscribed : ∃ h12 h23 h13,
      MT.case_split = Or.inl ⟨h12, h23, h13⟩) :
    ∀ v ∈ A, v ≠ MT.v1 → v ≠ MT.v2 → v ≠ MT.v3 →
      (if Problem97.OnArcOpposite MT.v1 MT.v2 MT.v3 v then 1 else 0)
        + (if Problem97.OnArcOpposite MT.v2 MT.v3 MT.v1 v then 1 else 0)
        + (if Problem97.OnArcOpposite MT.v3 MT.v1 MT.v2 v then 1 else 0)
        = 1 := by sorry
