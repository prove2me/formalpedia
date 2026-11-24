-- Prove2me | Theorems.Thm_ULHC_par_add_snd
-- name    : ULHC.par_add_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:59.164576+00:00
-- url     : https://prove2.me/theorems/d6424879-b920-4204-b97e-2e8a6cb06f8e
-- title:
--   ULHC: par add snd
-- statement:
--   The ULHC construction uses the par add snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Arcs.lean#L49-L50
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Arcs.lean#L49-L50

import Definitions.Def_ULHC_Potential
import Definitions.Def_ULHC_Arcs
set_option autoImplicit true
open ULHC

theorem ULHC.par_add_snd (c : Pt) : par (c.1, c.2 + 1) = !par c := by sorry
