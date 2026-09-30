-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionUpper_EnumerationProbe_toyMaximum_le_28_yukon_122fdfd0905d
-- name    : ProximityPrize.SubmissionUpper.EnumerationProbe.toyMaximum_le_28_yukon_122fdfd0905d
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-29T23:01:42.157095+00:00
-- url     : https://prove2.me/theorems/b363b34a-cdb4-490a-8aa8-0ff96f279f4b
-- title:
--   Small enumeration model: every key has at most 28 candidates
-- statement:
--   A kernel-checked enumeration of all eight-element subsets of fifteen nonidentity powers of a primitive sixteenth root modulo 17. Grouping by the first Newton coefficient and product exponent gives a maximum fiber size at most 28. This is a small model, not the full Better Codes bound.
--
--   Original contribution: jacklightChen, verified Better Codes submission 908984bd-7ffa-4003-8ee9-09ed8864e0ae. Source Lean 4.32.2, exact commit 4de021b74b21124943c35eeda5da5c891571ad3e. Statements, definitions and proof bodies preserved; imports and exported names adapted for Prove2Me.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/4de021b74b21124943c35eeda5da5c891571ad3e/ProximityPrize/SubmissionUpper/EnumerationProbe.lean
--
--   p2m-history-enumeration:20b9d32663fb8ff63d4974290623ae84be0ddecacfc8de41944f1ca0e8d8cdee
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwMm0taGlzdG9yeS1lbnVtZXJhdGlvbjoyMGI5ZDMyNjYzZmI4ZmY2M2Q0OTc0MjkwNjIzYWU4NGJlMGRkZWNhY2ZjOGRlNDE5NDRmMWNhMGU4ZDhjZGVlIiwiaGFzaCI6ImE4ODFhNjI2NzM5MTBhNjBlNjZmYjdhZGY0ZDY5MmE2OGIzZTNlYmZmNmU4MzQyZDhhYjkxOWEyNGViYzg4NDkiLCJraW5kIjoicHJvYmxlbSIsInRhcmdldCI6IlByb3hpbWl0eVByaXplLlN1Ym1pc3Npb25VcHBlci5FbnVtZXJhdGlvblByb2JlLnRveU1heGltdW1fbGVfMjhfeXVrb25fMTIyZmRmZDA5MDVkIiwiZW52aXJvbm1lbnQiOnsidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIiwibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQifSwidGFnIjoiYmV0dGVyLWNvZGVzLWhpc3RvcnkifQ]

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/



import Mathlib
import Definitions.Def_Yukon_d9f5b00d74e4bca418786f45
/-!
# A kernel-evaluated small analogue of the 1024-fold key map

This file deliberately leaves the scored construction unchanged.  It asks the
remote verifier to exhaust all eight-subsets of the fifteen nontrivial powers
of a primitive sixteenth root in `ZMod 17`, represented by natural residues.
The two key coordinates are the first Newton coefficient and the product
exponent modulo sixteen.  Candidates are traversed once while accumulating a
`16 × 17` histogram, so the expensive key calculation is not repeated for
every possible key.  A preceding remote smoke test established that this
histogram evaluates within the verifier budget, and a second run proved the
upper bounds 64, 44, 34, and 29, while a remote run proved that the bound 26 is
false.  This probe asks whether every fibre has size at most 28.
-/

namespace ProximityPrize.SubmissionUpper.EnumerationProbe

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem toyMaximum_le_28_yukon_122fdfd0905d : toyMaximum ≤ 28  := by sorry
end EnumerationProbe
end SubmissionUpper
end ProximityPrize
