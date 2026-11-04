-- Prove2me | Theorems.Thm_ThreeSum_OutputKeyMasks_eval_outside
-- name    : ThreeSum.OutputKeyMasks.eval_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:17:21.6312+00:00
-- url     : https://prove2.me/theorems/afdf71d2-24cb-4477-916d-826cf08aae99
-- title:
--   Output Key Masks: eval outside
-- statement:
--   The Output Key Masks construction uses the eval outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputKeyMasks.lean#L21-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputKeyMasks.lean#L21-L26

import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputKeyMasks
set_option autoImplicit false
open ThreeSum ThreeSum.OutputKeyMasks
open GlobalEncoding LocalHashMoments LocalCoverBounds
open OneHotMask SubsetAddress
open scoped BigOperators

theorem ThreeSum.OutputKeyMasks.eval_outside {L : ℕ} (Q : Finset (Fin L)) (w : Fin L → ℕ) :
    (eval (extend w) (fun _ => 0) L (subsetMask Q) : ℤ) =
      ∑ i : Fin L, if i ∈ Q then (0 : ℤ) else (w i : ℤ) := by sorry
