-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalRepeatedWords_ofFn_rev
-- name    : ThreeSum.WeightedGlobalRepeatedWords.ofFn_rev
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:20.050405+00:00
-- url     : https://prove2.me/theorems/a273c3ea-4de8-4c3d-92c8-b04bc72693a9
-- title:
--   Weighted Global Repeated Words: of Fn rev
-- statement:
--   The Weighted Global Repeated Words construction uses the of Fn rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatedWords.lean#L61-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatedWords.lean#L61-L69

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryWantedFactorial
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCoverWitness
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatedWords
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalRepeatedWords
open TernaryJointType Finset
open scoped BigOperators
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalRepeatedWords.ofFn_rev {A : Type*} {r : ℕ} (f : Fin r → A) :
    List.ofFn (fun i => f i.rev)=(List.ofFn f).reverse := by sorry
