-- Prove2me | Theorems.Thm_ULHC_par_sub_sub
-- name    : ULHC.par_sub_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:55:04.410817+00:00
-- url     : https://prove2.me/theorems/b6beb0f0-c1ed-492c-bba2-c5922ea016a8
-- title:
--   ULHC: par sub sub
-- statement:
--   The ULHC construction uses the par sub sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Arcs.lean#L52-L53
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Arcs.lean#L52-L53

import Definitions.Def_ULHC_Potential
import Definitions.Def_ULHC_Arcs
set_option autoImplicit true
open ULHC

theorem ULHC.par_sub_sub (c : Pt) : par (c.1 - 1, c.2 - 1) = par c := by sorry
