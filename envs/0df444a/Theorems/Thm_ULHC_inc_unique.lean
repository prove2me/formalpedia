-- Prove2me | Theorems.Thm_ULHC_inc_unique
-- name    : ULHC.inc_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:57:21.230808+00:00
-- url     : https://prove2.me/theorems/5ab7d372-4405-4d97-8abf-d907481ee763
-- title:
--   ULHC: inc unique
-- statement:
--   The ULHC construction uses the inc unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L388-L394
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L388-L394

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.inc_unique {F : Finset Edge} {y : Pt} (hd : deg F y = 1) {e e' : Edge} (he : e ∈ F)
    (hy : e.p = y ∨ e.q = y) (he' : e' ∈ F) (hy' : e'.p = y ∨ e'.q = y) : e' = e := by sorry
