-- Prove2me | Theorems.Thm_ULHC_outArc_nb_opp
-- name    : ULHC.outArc_nb_opp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:48:13.036097+00:00
-- url     : https://prove2.me/theorems/a40d29d9-dd5b-40ae-85f9-757d28e1eed5
-- title:
--   ULHC: out Arc nb opp
-- statement:
--   The ULHC construction uses the out Arc nb opp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean#L26-L29
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean#L26-L29

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.outArc_nb_opp (F : Finset Edge) (c : Pt) (s : Side) :
    outArc F (nb c s) s.opp = !outArc F c s := by sorry
