-- Prove2me | Theorems.Thm_ULHC_par_sub_snd
-- name    : ULHC.par_sub_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:28.972492+00:00
-- url     : https://prove2.me/theorems/87d843bd-c4e4-4b74-afc9-5cbe8e5702cb
-- title:
--   ULHC: par sub snd
-- statement:
--   The ULHC construction uses the par sub snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Arcs.lean#L43-L44
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Arcs.lean#L43-L44

import Definitions.Def_ULHC_Potential
import Definitions.Def_ULHC_Arcs
set_option autoImplicit true
open ULHC

theorem ULHC.par_sub_snd (c : Pt) : par (c.1, c.2 - 1) = !par c := by sorry
