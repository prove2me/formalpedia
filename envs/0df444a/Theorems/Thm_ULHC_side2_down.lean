-- Prove2me | Theorems.Thm_ULHC_side2_down
-- name    : ULHC.side2_down
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:01:07.857924+00:00
-- url     : https://prove2.me/theorems/ac5c3e3b-093b-4354-8cb7-1a64de97ddef
-- title:
--   ULHC: side2 down
-- statement:
--   The ULHC construction uses the side2 down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearChain.lean#L29-L31
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearChain.lean#L29-L31

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.side2_down (c : Pt) (s : Side) (j : ℕ) :
    nb (nb (cellJ c s (j + 1)) (latB s)) s.opp = nb (cellJ c s j) (latB s) := by sorry
