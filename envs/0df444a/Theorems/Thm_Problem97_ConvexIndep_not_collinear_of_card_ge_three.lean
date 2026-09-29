-- Prove2me | Theorems.Thm_Problem97_ConvexIndep_not_collinear_of_card_ge_three
-- name    : Problem97.ConvexIndep.not_collinear_of_card_ge_three
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T02:08:13.545942+00:00
-- url     : https://prove2.me/theorems/2bc1b598-8cf1-49ae-a11e-eff7a1601f56
-- title:
--   A convex-independent set with three points is noncollinear
-- statement:
--   Let $A$ be a finite convex-independent set in the Euclidean plane. If $|A|\ge 3$, then $A$ is not collinear. This packages the elementary fact that three collinear members would place one of them between the other two and hence inside the convex hull of the remaining points.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_ConvexIndep_not_collinear_of_card_ge_three.lean#L1-L47

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

theorem Problem97.ConvexIndep.not_collinear_of_card_ge_three {A : Finset ℝ²}
    (hA : ConvexIndep A) (hcard : 3 ≤ A.card) :
    ¬ Collinear ℝ (A : Set ℝ²) := by sorry
