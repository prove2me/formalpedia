-- Prove2me | Theorems.Thm_ULHC_par_add_fst
-- name    : ULHC.par_add_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:58.042973+00:00
-- url     : https://prove2.me/theorems/3ceb15e5-cf4e-4db4-8883-8688292d0f10
-- title:
--   ULHC: par add fst
-- statement:
--   The ULHC construction uses the par add fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Arcs.lean#L46-L47
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Arcs.lean#L46-L47

import Definitions.Def_ULHC_Potential
import Definitions.Def_ULHC_Arcs
set_option autoImplicit true
open ULHC

theorem ULHC.par_add_fst (c : Pt) : par (c.1 + 1, c.2) = !par c := by sorry
