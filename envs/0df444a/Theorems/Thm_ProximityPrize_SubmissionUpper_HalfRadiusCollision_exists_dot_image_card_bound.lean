-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionUpper_HalfRadiusCollision_exists_dot_image_card_bound
-- name    : ProximityPrize.SubmissionUpper.HalfRadiusCollision.exists_dot_image_card_bound
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-27T05:54:19.532524+00:00
-- url     : https://prove2.me/theorems/1e41859c-6cf7-459a-9fd9-59d2ebf6d7be
-- title:
--   ProximityPrize.SubmissionUpper.HalfRadiusCollision.exists_dot_image_card_bound
-- statement:
--   A dot-product map with a lower bound on its image cardinality.
--
--   Original Proximity Prize source by GitHub contributor erdkocak; preserved in upper submission bd59768c-5fe4-466a-a8f2-e94a39ae4d4a (224323f053d0d1dfa78d7b9625194fe0133f04bc). Ported from Lean 4.32.2 to 4.33.1 with independently checked statements, full source and target kernel replay, quotient checks and transitive axiom checks. This provider publication is not a new competition submission.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/224323f053d0d1dfa78d7b9625194fe0133f04bc/ProximityPrize/SubmissionUpper/HalfRadiusCollision.lean
--
--   yukon-proof-operation:bootstrap-f2d259c679cac6dcc1a4b81c4713de583adc12930337e79de52fcfa780b5f012
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246Ym9vdHN0cmFwLWYyZDI1OWM2NzljYWM2ZGNjMWE0YjgxYzQ3MTNkZTU4M2FkYzEyOTMwMzM3ZTc5ZGU1MmZjZmE3ODBiNWYwMTIiLCJoYXNoIjoiMjE4YTMxYTFjZjY5NmZkNDMzYTg1YzJmOWY1ZjVmYjM5MmNhMzEwMjI4MjlmYmQ1YmNlYjU3MjE2MjIxYjk1MyIsImtpbmQiOiJwcm9ibGVtIiwidGFyZ2V0IjoiUHJveGltaXR5UHJpemUuU3VibWlzc2lvblVwcGVyLkhhbGZSYWRpdXNDb2xsaXNpb24uZXhpc3RzX2RvdF9pbWFnZV9jYXJkX2JvdW5kIiwiZW52aXJvbm1lbnQiOnsidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIiwibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQifSwidGFnIjoicHJveGltaXR5LXByaXplIn0]

import Mathlib
import Init
import Definitions.Def_ProximityPrize_SubmissionUpper_HalfRadiusCollision_dot
namespace ProximityPrize.SubmissionUpper.HalfRadiusCollision

open scoped BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Some linear functional has an image whose density is at least
`|A| / (|F| + |A| - 1)`.  This is the quantitative form of the collision
argument: unlike `exists_dot_surjective_of_card_sq_lt`, it does not require the
image to be all of `F`. -/
theorem exists_dot_image_card_bound {k : ℕ} (A : Finset (Fin k → F)) :
    ∃ v : Fin k → F,
      A.card * Fintype.card F ≤
        (A.image (fun x => dot x v)).card * (Fintype.card F + A.card - 1) := by sorry
end HalfRadiusCollision
end SubmissionUpper
end ProximityPrize
