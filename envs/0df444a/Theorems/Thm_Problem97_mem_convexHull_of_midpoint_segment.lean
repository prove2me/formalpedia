-- Prove2me | Theorems.Thm_Problem97_mem_convexHull_of_midpoint_segment
-- name    : Problem97.mem_convexHull_of_midpoint_segment
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:56:14.119709+00:00
-- url     : https://prove2.me/theorems/e37f6906-be27-4c54-998d-1f62dd08a49a
-- title:
--   A midpoint-to-vertex segment lies in the three-point convex hull
-- statement:
--   Let $x,y,a,b$ be points in the Euclidean plane. If $a$ lies on the closed segment joining the midpoint of $x$ and $y$ to $b$, then $a$ lies in the convex hull of $\{x,y,b\}$. This supplies the convex-hull step used to turn a same-ray perpendicular-bisector configuration into a contradiction with convex independence.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_mem_convexHull_of_midpoint_segment.lean#L1-L47

/- Generated theorem stub from Erdos9796Proof.P97.ConvexIndepHelpers by Stage 2 proof cut; source SHA-256 58fea6fdfc458ff582e9e12c324d10b6e51a5653a6daa5dc80f586642be49129 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
open Problem97



/-!
# `ConvexIndep` Finset helpers (Milestone 2)

Direct proofs from the extreme-point characterization
`EuclideanGeometry.ConvexIndep S ↔ ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})`:

* `ConvexIndep.mono` — `B ⊆ A → ConvexIndep A → ConvexIndep B`
* `ConvexIndep.erase` — `ConvexIndep A → ConvexIndep (A.erase x)`

These power the M4 descent step: erasing a removable vertex from a
counterexample preserves convex independence, and more generally any
subset of a convex-independent set is convex independent.
-/

open scoped EuclideanGeometry

theorem Problem97.mem_convexHull_of_midpoint_segment {x y a b : ℝ²}
    (h : a ∈ segment ℝ (midpoint ℝ x y) b) :
    a ∈ convexHull ℝ ({x, y, b} : Set ℝ²) := by sorry
