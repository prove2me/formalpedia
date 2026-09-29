-- Prove2me | Theorems.Thm_Problem97_ConvexIndep_not_wbtw
-- name    : Problem97.ConvexIndep.not_wbtw
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:55:43.214885+00:00
-- url     : https://prove2.me/theorems/c8d80ad1-f5cb-40e4-9834-e427b03ec13b
-- title:
--   Convex Independence Excludes Weak Betweenness
-- statement:
--   If A is convex-independent and x,y,z belong to A, with y distinct from x and z, then y cannot lie weakly between x and z.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_ConvexIndep_not_wbtw.lean#L1-L47

/- Generated theorem stub from Erdos9796Proof.P97.ConvexIndepHelpers by Stage 2 proof cut; source SHA-256 58fea6fdfc458ff582e9e12c324d10b6e51a5653a6daa5dc80f586642be49129 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
open Problem97 Problem97.ConvexIndep



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

theorem Problem97.ConvexIndep.not_wbtw {A : Finset ℝ²} (hA : ConvexIndep A)
    {x y z : ℝ²} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (hxy : Wbtw ℝ x y z) (hyx : y ≠ x) (hyz : y ≠ z) : False := by sorry
