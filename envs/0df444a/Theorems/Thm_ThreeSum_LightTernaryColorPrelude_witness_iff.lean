-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryColorPrelude_witness_iff
-- name    : ThreeSum.LightTernaryColorPrelude.witness_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:39:21.975899+00:00
-- url     : https://prove2.me/theorems/66f38d76-16e3-4b6a-b389-ec0906407e3b
-- title:
--   Light Ternary Color Prelude: witness iff
-- statement:
--   The Light Ternary Color Prelude construction uses the witness iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryColorPrelude.lean#L302-L313
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryColorPrelude.lean#L302-L313

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Theorems.Thm_ThreeSum_ColorClassLists_witness_iff

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryColorPrelude
open Light ColorClassLists LightColorParametersCosts
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryColorPrelude.witness_iff {n : ℕ} {p : Coloring.Parameter (width n)} {x : Fin n→ℤ}
    {μ : ℕ→ℤ} {ab bb cb : ℕ} {A B C : List ℤ}
    (hA : Normalized μ ab n (classList p x 0 1) A)
    (hB : Normalized μ bb n (classList p x 1 1) B)
    (hC : Normalized μ cb n (classList p x 2 (-1)) C) :
    witness A B C↔ColorClassLists.witness p x := by sorry
