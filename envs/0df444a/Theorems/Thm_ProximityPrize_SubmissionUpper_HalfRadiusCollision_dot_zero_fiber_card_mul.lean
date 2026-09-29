-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionUpper_HalfRadiusCollision_dot_zero_fiber_card_mul
-- name    : ProximityPrize.SubmissionUpper.HalfRadiusCollision.dot_zero_fiber_card_mul
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-27T04:35:17.216301+00:00
-- url     : https://prove2.me/theorems/2edd7028-34cc-4274-8fff-4e3e6ce8deeb
-- title:
--   ProximityPrize.SubmissionUpper.HalfRadiusCollision.dot_zero_fiber_card_mul
-- statement:
--   For a nonzero vector over a finite field, the size of the zero fiber of its dot product, multiplied by the field size, equals the size of the vector space.
--
--   Original Proximity Prize source by GitHub contributor gpsanant; preserved in the verified upper submission by erdkocak (224323f053d0d1dfa78d7b9625194fe0133f04bc). Ported from Lean 4.32.2 to 4.33.1 with independently checked statements, full source and target kernel replay, quotient checks and transitive axiom checks. This provider publication is not a new competition submission.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/a36cdb6a0c9be507b70276a92129bb15d4ed2a27/ProximityPrize/SubmissionUpper/HalfRadiusCollision.lean
--
--   yukon-proof-operation:bootstrap-2fdc2c314e240aae57257d57c9cc4248f655d5bcfb542a9aef8ab231b6586357
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246Ym9vdHN0cmFwLTJmZGMyYzMxNGUyNDBhYWU1NzI1N2Q1N2M5Y2M0MjQ4ZjY1NWQ1YmNmYjU0MmE5YWVmOGFiMjMxYjY1ODYzNTciLCJoYXNoIjoiNzRhOWRkZDE5NGVlNDgyNzJjNGYyYTBlMjMyNzRlNGVkNjFmMmQxZTg4MmI5YTM5MWQ0YmNmMmEzY2M3NDE4YyIsImtpbmQiOiJwcm9ibGVtIiwidGFyZ2V0IjoiUHJveGltaXR5UHJpemUuU3VibWlzc2lvblVwcGVyLkhhbGZSYWRpdXNDb2xsaXNpb24uZG90X3plcm9fZmliZXJfY2FyZF9tdWwiLCJlbnZpcm9ubWVudCI6eyJ0b29sY2hhaW4iOiJsZWFucHJvdmVyL2xlYW40OnY0LjMzLjEiLCJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCJ9LCJ0YWciOiJwcm94aW1pdHktcHJpemUifQ]

import Mathlib
import Init
import Definitions.Def_ProximityPrize_SubmissionUpper_HalfRadiusCollision_dot
namespace ProximityPrize.SubmissionUpper.HalfRadiusCollision

open scoped BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

lemma dot_zero_fiber_card_mul {k : ℕ} {d : Fin k → F} (hd : d ≠ 0) :
    ((Finset.univ.filter fun v : Fin k → F => dot d v = 0).card) * Fintype.card F =
      Fintype.card (Fin k → F) := by sorry
end HalfRadiusCollision
end SubmissionUpper
end ProximityPrize
