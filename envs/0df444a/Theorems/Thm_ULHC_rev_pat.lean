-- Prove2me | Theorems.Thm_ULHC_rev_pat
-- name    : ULHC.rev_pat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:57:52.767988+00:00
-- url     : https://prove2.me/theorems/6a1f5f70-1217-49f9-afde-984154bba01c
-- title:
--   ULHC: rev pat
-- statement:
--   The ULHC construction uses the rev pat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reverse.lean#L62-L73
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reverse.lean#L62-L73

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_Reverse
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hk : k % 2 = 0) (hpat : StripPat F c s (k + 2))
include hk hpat

theorem ULHC.rev_pat : StripPat (flipCol F c s (k + 2)) (cellJ c s (k + 1)) s.opp (k + 2) := by sorry
