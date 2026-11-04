-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_supportPairs_update_zero
-- name    : ThreeSum.TernaryCodeSemantics.supportPairs_update_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:33.682197+00:00
-- url     : https://prove2.me/theorems/c8c854d5-53a8-4984-a354-58a4a1c00dd7
-- title:
--   Ternary Code Semantics: support Pairs update zero
-- statement:
--   The Ternary Code Semantics construction uses the support Pairs update zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L119-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L119-L124

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryCodeSemantics.supportPairs_update_zero {N : ℕ} (w : TritWord N) (i : Fin N) :
    supportPairs (Function.update w i 0)=
      ((supportPairs w).erase (i,1)).erase (i,0) := by sorry
