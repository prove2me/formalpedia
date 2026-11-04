-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryInversePass_values_eq_coordinateInverse
-- name    : ThreeSum.LightTernaryInversePass.values_eq_coordinateInverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:56:10.704622+00:00
-- url     : https://prove2.me/theorems/547dbb23-98a1-417b-868e-79fc7766a45c
-- title:
--   Light Ternary Inverse Pass: values eq coordinate Inverse
-- statement:
--   A semantic bridge from the compact metadata to the exact coordinate stage.
--   Only lower digit metadata must agree; higher slots can duplicate an address.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryInversePass.lean#L42-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryInversePass.lean#L42-L56

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryInversePass
set_option maxHeartbeats 2000000
open Light ThreeSum.TernaryQuery ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryInversePass.values_eq_coordinateInverse {N : ℕ} (enumeration : ℕ →
    ThreeSum.TernaryJointType.TritWord N) (i : Fin N)
    (digits : ℕ → Fin 3) (ix : Fin 3 → ℕ → ℕ)
    (F : ThreeSum.TernaryJointType.TritWord N → ℤ) (j : ℕ)
    (hdigit : digits j = enumeration j i)
    (hindex : ∀ e ≤ digits j, enumeration (ix e j) =
      Function.update (enumeration j) i e) :
    values digits ix (fun k => F (enumeration k)) j =
      coordinateInverse i F (enumeration j) := by sorry
