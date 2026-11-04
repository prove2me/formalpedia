-- Prove2me | Theorems.Thm_ThreeSum_RawAKeyLists_raw_wanted_mem
-- name    : ThreeSum.RawAKeyLists.raw_wanted_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:51:45.532961+00:00
-- url     : https://prove2.me/theorems/8090956f-7e2f-443e-9546-611966faee49
-- title:
--   Raw AKey Lists: raw wanted mem
-- statement:
--   The Raw AKey Lists construction uses the raw wanted mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L139-L147
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L139-L147

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000

theorem ThreeSum.RawAKeyLists.raw_wanted_mem {h J : ℕ} {P d : ℤ} {xs : List ℤ}
    {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {T : Finset (Original (Fin xs.length) β γ)} {b : β → ℤ} {c : γ → ℤ}
    {r : RawItem h J (Fin xs.length) β γ}
    (hr : r ∈ rawOn h J P d T (fun i => xs.getD i.val 0) b c) :
    RawReporting.wantedOf r ∈ wanted (localPrime h^J) P xs h J d := by sorry
