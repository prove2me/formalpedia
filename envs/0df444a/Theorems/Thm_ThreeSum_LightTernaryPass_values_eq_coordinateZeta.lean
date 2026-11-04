-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPass_values_eq_coordinateZeta
-- name    : ThreeSum.LightTernaryPass.values_eq_coordinateZeta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:37.049518+00:00
-- url     : https://prove2.me/theorems/c9fa7fca-9aa0-4aa9-809c-3da5723b5b94
-- title:
--   Light Ternary Pass: values eq coordinate Zeta
-- statement:
--   A semantic bridge from the compact metadata to the exact coordinate stage.
--   Only lower digit metadata must agree; higher slots can duplicate an address.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPass.lean#L39-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPass.lean#L39-L53

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPass
set_option maxHeartbeats 2000000
open Light ThreeSum.TernaryQuery ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryPass.values_eq_coordinateZeta {N : ℕ} (enumeration : ℕ →
    ThreeSum.TernaryJointType.TritWord N) (i : Fin N)
    (digits : ℕ → Fin 3) (ix : Fin 3 → ℕ → ℕ)
    (F : ThreeSum.TernaryJointType.TritWord N → ℤ) (j : ℕ)
    (hdigit : digits j = enumeration j i)
    (hindex : ∀ e ≤ digits j, enumeration (ix e j) =
      Function.update (enumeration j) i e) :
    values digits ix (fun k => F (enumeration k)) j =
      coordinateZeta i F (enumeration j) := by sorry
