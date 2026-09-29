-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionUpper_HalfRadiusCollision_dot_surjective
-- name    : ProximityPrize.SubmissionUpper.HalfRadiusCollision.dot_surjective
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-27T04:31:48.653451+00:00
-- url     : https://prove2.me/theorems/913f2723-3fce-41d5-824c-c1f5a53e461d
-- title:
--   ProximityPrize.SubmissionUpper.HalfRadiusCollision.dot_surjective
-- statement:
--   Dot product against a nonzero vector is surjective over a field.
--
--   Original Proximity Prize source by GitHub contributor gpsanant; preserved in the verified upper submission by erdkocak (224323f053d0d1dfa78d7b9625194fe0133f04bc). Ported from Lean 4.32.2 to 4.33.1 with independently checked statements, full source and target kernel replay, quotient checks and transitive axiom checks. This provider publication is not a new competition submission.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/a36cdb6a0c9be507b70276a92129bb15d4ed2a27/ProximityPrize/SubmissionUpper/HalfRadiusCollision.lean
--
--   yukon-proof-operation:bootstrap-c2eff4e2bf3e17c09fc382f29e1017d90e81940bf703c09d92a5fc649fcbe890
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246Ym9vdHN0cmFwLWMyZWZmNGUyYmYzZTE3YzA5ZmMzODJmMjllMTAxN2Q5MGU4MTk0MGJmNzAzYzA5ZDkyYTVmYzY0OWZjYmU4OTAiLCJoYXNoIjoiMGNhYmUxMmI3ZGE2OWJkYTMyMmExMmIzZmVkY2YyNTBhOWIzN2RmZjY4MDJlYTljZjBlNzVjMTdlM2U1NTNhZSIsImtpbmQiOiJwcm9ibGVtIiwidGFyZ2V0IjoiUHJveGltaXR5UHJpemUuU3VibWlzc2lvblVwcGVyLkhhbGZSYWRpdXNDb2xsaXNpb24uZG90X3N1cmplY3RpdmUiLCJlbnZpcm9ubWVudCI6eyJ0b29sY2hhaW4iOiJsZWFucHJvdmVyL2xlYW40OnY0LjMzLjEiLCJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCJ9LCJ0YWciOiJwcm94aW1pdHktcHJpemUifQ]

import Mathlib
import Init
import Definitions.Def_ProximityPrize_SubmissionUpper_HalfRadiusCollision_dot
namespace ProximityPrize.SubmissionUpper.HalfRadiusCollision

open scoped BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
lemma dot_surjective {k : ℕ} {d : Fin k → F} (hd : d ≠ 0) :
    Function.Surjective (dot d) := by sorry
end HalfRadiusCollision
end SubmissionUpper
end ProximityPrize
