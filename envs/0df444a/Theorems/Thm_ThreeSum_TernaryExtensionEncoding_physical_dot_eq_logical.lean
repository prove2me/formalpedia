-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_physical_dot_eq_logical
-- name    : ThreeSum.TernaryExtensionEncoding.physical_dot_eq_logical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:47.047113+00:00
-- url     : https://prove2.me/theorems/3f7ddb14-7be0-4983-8caa-602076825546
-- title:
--   Ternary Extension Encoding: physical dot eq logical
-- statement:
--   The Ternary Extension Encoding construction uses the physical dot eq logical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalKeyCodes.lean#L31-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalKeyCodes.lean#L31-L33

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryExtensionEncoding.physical_dot_eq_logical (J : ℕ) (raw coeff : Fin (J+2) → ZMod p) :
    (∑ i, raw (digitOrder J i)*coeff (digitOrder J i))=∑ i, raw i*coeff i := by sorry
