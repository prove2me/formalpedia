-- Prove2me | Theorems.Thm_ULHC_par_sub_fst
-- name    : ULHC.par_sub_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:21.46668+00:00
-- url     : https://prove2.me/theorems/7176eabb-5332-440f-9205-dd668567d217
-- title:
--   ULHC: par sub fst
-- statement:
--   The ULHC construction uses the par sub fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Arcs.lean#L40-L41
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Arcs.lean#L40-L41

import Definitions.Def_ULHC_Potential
import Definitions.Def_ULHC_Arcs
set_option autoImplicit true
open ULHC

theorem ULHC.par_sub_fst (c : Pt) : par (c.1 - 1, c.2) = !par c := by sorry
