-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryColorPrelude_witness_sound
-- name    : ThreeSum.LightTernaryColorPrelude.witness_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:39:58.158127+00:00
-- url     : https://prove2.me/theorems/a25279a7-a54a-4ee0-82d8-c6bd1e4c1d38
-- title:
--   Light Ternary Color Prelude: witness sound
-- statement:
--   The Light Ternary Color Prelude construction uses the witness sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryColorPrelude.lean#L336-L344
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryColorPrelude.lean#L336-L344

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Theorems.Thm_ThreeSum_RawIncidences_witness_sound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryColorPrelude
open Light ColorClassLists LightColorParametersCosts
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryColorPrelude.witness_sound {n : ℕ} {p : Coloring.Parameter (width n)} {x : Fin n→ℤ}
    {μ : ℕ→ℤ} {ab bb cb : ℕ} {A B C : List ℤ}
    (hA : Normalized μ ab n (classList p x 0 1) A)
    (hB : Normalized μ bb n (classList p x 1 1) B)
    (hC : Normalized μ cb n (classList p x 2 (-1)) C)
    (H : witness A B C) : Coloring.DistinctZeroSum x := by sorry
