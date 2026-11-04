-- Prove2me | Theorems.Thm_ThreeSum_LightMomentZeroDetector_moment_abs_bound
-- name    : ThreeSum.LightMomentZeroDetector.moment_abs_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:04:36.314057+00:00
-- url     : https://prove2.me/theorems/1fb0e19d-6c9d-495d-a809-ec01f189dcf9
-- title:
--   Light Moment Zero Detector: moment abs bound
-- statement:
--   Ordinary polynomial bounds on the physical moments suffice; no multiword
--   arithmetic or denominator representation is used by the detector.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L116-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L116-L128

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector
open scoped BigOperators

theorem ThreeSum.LightMomentZeroDetector.moment_abs_bound {t H k : ℕ} (v w : Fin t → ℤ) (V : ℤ)
    (hV : 1≤V) (hv : ∀ s, |v s|≤V) (hk : k≤2*H) :
    |moment v w k|≤(∑ s, |w s|)*V^(2*H) := by sorry
