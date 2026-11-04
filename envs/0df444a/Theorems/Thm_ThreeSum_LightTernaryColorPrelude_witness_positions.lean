-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryColorPrelude_witness_positions
-- name    : ThreeSum.LightTernaryColorPrelude.witness_positions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:38:51.278925+00:00
-- url     : https://prove2.me/theorems/b5e349be-663f-43eb-ab48-5ff8958ec282
-- title:
--   Light Ternary Color Prelude: witness positions
-- statement:
--   Any witness in the physically normalized arrays comes from three
--   different original positions, even when original input values repeat.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryColorPrelude.lean#L317-L334
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryColorPrelude.lean#L317-L334

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryColorPrelude
open Light ColorClassLists LightColorParametersCosts
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryColorPrelude.witness_positions {n : ℕ} {p : Coloring.Parameter (width n)} {x : Fin n→ℤ}
    {μ : ℕ→ℤ} {ab bb cb : ℕ} {A B C : List ℤ}
    (hA : Normalized μ ab n (classList p x 0 1) A)
    (hB : Normalized μ bb n (classList p x 1 1) B)
    (hC : Normalized μ cb n (classList p x 2 (-1)) C)
    {a b c : ℤ} (ha : a∈A) (hb : b∈B) (hc : c∈C) (he : c-b=a) :
    ∃ i j k : Fin n, i≠j ∧ i≠k ∧ j≠k ∧ x i=a ∧ x j=b ∧ -x k=c ∧ x i+x j+x k=0 := by sorry
