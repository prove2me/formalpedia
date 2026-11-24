-- Prove2me | Theorems.Thm_ULHC_pat_flip_pair
-- name    : ULHC.pat_flip_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:40:34.651617+00:00
-- url     : https://prove2.me/theorems/a104b704-b486-4feb-b19f-c2e8d4deb489
-- title:
--   ULHC: pat flip pair
-- statement:
--   The ULHC construction uses the pat flip pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L348-L380
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L348-L380

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
open ULHC
open Finset Classical
variable {F : Finset Edge} {c : Pt} {s : Side}

theorem ULHC.pat_flip_pair {k : ℕ} (hk : k % 2 = 0) (h : StripPat F c s (k + 3)) :
    StripPat (flip (flip F (cellJ c s (k + 2))) (cellJ c s (k + 1))) c s (k + 1) := by sorry
