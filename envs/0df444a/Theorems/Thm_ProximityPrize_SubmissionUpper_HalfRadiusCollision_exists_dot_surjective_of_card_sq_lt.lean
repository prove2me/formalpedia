-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionUpper_HalfRadiusCollision_exists_dot_surjective_of_card_sq_lt
-- name    : ProximityPrize.SubmissionUpper.HalfRadiusCollision.exists_dot_surjective_of_card_sq_lt
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-27T06:04:39.701783+00:00
-- url     : https://prove2.me/theorems/6264a1ca-1e59-443a-9457-272d446837c7
-- title:
--   ProximityPrize.SubmissionUpper.HalfRadiusCollision.exists_dot_surjective_of_card_sq_lt
-- statement:
--   Existence of a surjective dot-product map under a finite-field cardinality bound.
--
--   Original Proximity Prize source by GitHub contributor gpsanant; preserved in upper submission bd59768c-5fe4-466a-a8f2-e94a39ae4d4a (224323f053d0d1dfa78d7b9625194fe0133f04bc). Ported from Lean 4.32.2 to 4.33.1 with independently checked statements, full source and target kernel replay, quotient checks and transitive axiom checks. This provider publication is not a new competition submission.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/a36cdb6a0c9be507b70276a92129bb15d4ed2a27/ProximityPrize/SubmissionUpper/HalfRadiusCollision.lean
--
--   yukon-proof-operation:bootstrap-fe92fbf1dd96753a744079ce1ebc4faa0ce39881857a9b8ae0b849b60d101b26
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246Ym9vdHN0cmFwLWZlOTJmYmYxZGQ5Njc1M2E3NDQwNzljZTFlYmM0ZmFhMGNlMzk4ODE4NTdhOWI4YWUwYjg0OWI2MGQxMDFiMjYiLCJoYXNoIjoiNzk3NWU3OWM2NmUwY2EzYzgwYjNlMDVmZThlOGNlNDRiM2ZiNmRjNjNkZDZlZGQ5ZGQwZDdmNWYyNjU1NmMxNCIsImtpbmQiOiJwcm9ibGVtIiwidGFyZ2V0IjoiUHJveGltaXR5UHJpemUuU3VibWlzc2lvblVwcGVyLkhhbGZSYWRpdXNDb2xsaXNpb24uZXhpc3RzX2RvdF9zdXJqZWN0aXZlX29mX2NhcmRfc3FfbHQiLCJlbnZpcm9ubWVudCI6eyJ0b29sY2hhaW4iOiJsZWFucHJvdmVyL2xlYW40OnY0LjMzLjEiLCJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCJ9LCJ0YWciOiJwcm94aW1pdHktcHJpemUifQ]

import Mathlib
import Init
import Definitions.Def_ProximityPrize_SubmissionUpper_HalfRadiusCollision_dot
namespace ProximityPrize.SubmissionUpper.HalfRadiusCollision

open scoped BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem exists_dot_surjective_of_card_sq_lt {k : ℕ} (A : Finset (Fin k → F))
    (hlarge : (Fintype.card F - 1) ^ 2 < A.card) :
    ∃ v : Fin k → F, A.image (fun x => dot x v) = Finset.univ := by sorry
end HalfRadiusCollision
end SubmissionUpper
end ProximityPrize
