-- Prove2me | Theorems.Thm_ULHC_nb_nb_opp
-- name    : ULHC.nb_nb_opp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:23:09.164833+00:00
-- url     : https://prove2.me/theorems/1a67a881-39f1-49cc-a318-fee99c458b39
-- title:
--   ULHC: nb nb opp
-- statement:
--   The ULHC construction uses the nb nb opp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean#L57-L58
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean#L57-L58

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.nb_nb_opp (c : Pt) (s : Side) : nb (nb c s) s.opp = c := by sorry
