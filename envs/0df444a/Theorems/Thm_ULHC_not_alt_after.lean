-- Prove2me | Theorems.Thm_ULHC_not_alt_after
-- name    : ULHC.not_alt_after
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:44:08.236734+00:00
-- url     : https://prove2.me/theorems/90a8db61-41e7-4e88-a9f3-9f4410b0042a
-- title:
--   ULHC: not alt after
-- statement:
--   The ULHC construction uses the not alt after property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L171-L188
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L171-L188

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hk : k % 2 = 0) (hpat : StripPat F c s (k + 2))
include hk hpat

theorem ULHC.not_alt_after {j : ℕ} (hj : 1 ≤ j) (hj' : j ≤ k + 1) :
    ¬ Alt (flipCol F c s (k + 2)) (cellJ c s j) := by sorry
