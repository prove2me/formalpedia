-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_support_subset
-- name    : ThreeSum.TernaryCodeSemantics.support_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:40:12.450617+00:00
-- url     : https://prove2.me/theorems/565cdc33-bc2f-4086-9235-ae96c73c4c6b
-- title:
--   Ternary Code Semantics: support subset
-- statement:
--   The Ternary Code Semantics construction uses the support subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L48-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L48-L51

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryCodeSemantics.support_subset {N : ℕ} (w : TritWord N) : support w ⊆ range (2*N) := by sorry
