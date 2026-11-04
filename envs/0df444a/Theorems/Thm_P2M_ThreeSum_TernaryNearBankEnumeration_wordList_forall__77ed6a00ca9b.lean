-- Prove2me | Theorems.Thm_P2M_ThreeSum_TernaryNearBankEnumeration_wordList_forall__77ed6a00ca9b
-- name    : P2M_ThreeSum_TernaryNearBankEnumeration_wordList_forall__77ed6a00ca9b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:38:10.358192+00:00
-- url     : https://prove2.me/theorems/6455b21f-d3d3-4da7-87e4-5536a9763683
-- title:
--   P2 M Three Sum Ternary Near Bank Enumeration word List forall  77ed6a00ca9b: P2 M Three Sum Ternary Near Bank Enumeration word List forall  77ed6a00ca9b
-- statement:
--   The P2 M Three Sum Ternary Near Bank Enumeration word List forall  77ed6a00ca9b construction uses the P2 M Three Sum Ternary Near Bank Enumeration word List forall  77ed6a00ca9b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearBankEnumeration.lean#L11-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearBankEnumeration.lean#L11-L24

import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration

theorem P2M_ThreeSum_TernaryNearBankEnumeration_wordList_forall__77ed6a00ca9b {N : ℕ} (R Q : TritWord N) :
    List.Forall₂ (· ≤ ·) (wordList R) (wordList Q) ↔ Below R Q := by sorry

alias «ThreeSum».«TernaryNearBankEnumeration».«wordList_forall₂» := P2M_ThreeSum_TernaryNearBankEnumeration_wordList_forall__77ed6a00ca9b
