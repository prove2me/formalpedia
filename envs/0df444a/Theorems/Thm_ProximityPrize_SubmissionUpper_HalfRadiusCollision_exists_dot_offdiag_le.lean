-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionUpper_HalfRadiusCollision_exists_dot_offdiag_le
-- name    : ProximityPrize.SubmissionUpper.HalfRadiusCollision.exists_dot_offdiag_le
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-27T05:07:33.824288+00:00
-- url     : https://prove2.me/theorems/7147b4f6-3728-4b8c-ba87-bce187ce40a5
-- title:
--   ProximityPrize.SubmissionUpper.HalfRadiusCollision.exists_dot_offdiag_le
-- statement:
--   Averaging bound for off-diagonal collisions of a finite-field dot product.
--
--   Original Proximity Prize source by GitHub contributor gpsanant; preserved in upper submission bd59768c-5fe4-466a-a8f2-e94a39ae4d4a (224323f053d0d1dfa78d7b9625194fe0133f04bc). Ported from Lean 4.32.2 to 4.33.1 with independently checked statements, full source and target kernel replay, quotient checks and transitive axiom checks. This provider publication is not a new competition submission.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/a36cdb6a0c9be507b70276a92129bb15d4ed2a27/ProximityPrize/SubmissionUpper/HalfRadiusCollision.lean
--
--   yukon-proof-operation:bootstrap-0d3295cb42d2ce5ccfb30bc211a381dec3e86ef5121ef5f8ed9f3265875af4a5
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246Ym9vdHN0cmFwLTBkMzI5NWNiNDJkMmNlNWNjZmIzMGJjMjExYTM4MWRlYzNlODZlZjUxMjFlZjVmOGVkOWYzMjY1ODc1YWY0YTUiLCJoYXNoIjoiNDYyN2QyNzkzMWM2NzQyMmY5ODc0Zjc2MTA5ZDdkMGQ3MWEyM2ZiMDVjMTQzMGViOTliNzYxMzIzYWQyZWYzOCIsImtpbmQiOiJwcm9ibGVtIiwidGFyZ2V0IjoiUHJveGltaXR5UHJpemUuU3VibWlzc2lvblVwcGVyLkhhbGZSYWRpdXNDb2xsaXNpb24uZXhpc3RzX2RvdF9vZmZkaWFnX2xlIiwiZW52aXJvbm1lbnQiOnsidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIiwibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQifSwidGFnIjoicHJveGltaXR5LXByaXplIn0]

import Mathlib
import Init
import Definitions.Def_ProximityPrize_SubmissionUpper_HalfRadiusCollision_dot
namespace ProximityPrize.SubmissionUpper.HalfRadiusCollision

open scoped BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

lemma exists_dot_offdiag_le {k : ℕ} (A : Finset (Fin k → F)) :
    ∃ v : Fin k → F,
      Fintype.card F *
          ((A.product A).filter fun xy =>
            xy.1 ≠ xy.2 ∧ dot xy.1 v = dot xy.2 v).card ≤
        A.card * (A.card - 1) := by sorry
end HalfRadiusCollision
end SubmissionUpper
end ProximityPrize
