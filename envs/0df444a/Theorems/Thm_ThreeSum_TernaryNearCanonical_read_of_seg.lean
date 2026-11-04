-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearCanonical_read_of_seg
-- name    : ThreeSum.TernaryNearCanonical.read_of_seg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:10:49.553032+00:00
-- url     : https://prove2.me/theorems/fb5361f7-9b61-49ae-8f1a-938b91de460f
-- title:
--   Ternary Near Canonical: read of seg
-- statement:
--   The Ternary Near Canonical construction uses the read of seg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L60-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean#L60-L66

import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryNearCanonical.read_of_seg {N D a : ℕ} (Q : TritWord N) (μ : ℕ → ℤ)
    (hseg : Light.Seg μ a ((TernaryNearEnumeration.codes (wordList Q) D).map (fun c => (c : ℤ)))) :
    ∀ j<(TernaryNearEnumeration.codes (wordList Q) D).length,
      μ (a+j)=(address (word Q D j) : ℤ) := by sorry
