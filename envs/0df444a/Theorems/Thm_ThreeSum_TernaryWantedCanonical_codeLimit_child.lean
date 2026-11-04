-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedCanonical_codeLimit_child
-- name    : ThreeSum.TernaryWantedCanonical.codeLimit_child
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:29:23.798205+00:00
-- url     : https://prove2.me/theorems/df7483c4-458e-4de0-8317-e92876413b76
-- title:
--   Ternary Wanted Canonical: code Limit child
-- statement:
--   The Ternary Wanted Canonical construction uses the code Limit child property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonical.lean#L34-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonical.lean#L34-L39

import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
import Theorems.Thm_ThreeSum_TernaryWantedRadix_codeLimit_child

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedCanonical
open TernaryWantedRadix

theorem ThreeSum.TernaryWantedCanonical.codeLimit_child {N code R j digit : ℕ} (hN : 1 ≤ N) (hdigit : digit < R) :
    codeLimit N (code*R+digit) R j ≤ codeLimit N code R (j+1) := by sorry
