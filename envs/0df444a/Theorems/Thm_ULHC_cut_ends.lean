-- Prove2me | Theorems.Thm_ULHC_cut_ends
-- name    : ULHC.cut_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:43:39.308812+00:00
-- url     : https://prove2.me/theorems/62868e9f-f913-4155-a91f-c841af46e2ed
-- title:
--   ULHC: cut ends
-- statement:
--   The ULHC construction uses the cut ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L105-L108
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L105-L108

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.cut_ends {P : Finset Pt} {e : Edge} {a b : Pt} (h : Ends e a b) :
    Cut P e ↔ (a ∈ P ↔ b ∉ P) := by sorry
