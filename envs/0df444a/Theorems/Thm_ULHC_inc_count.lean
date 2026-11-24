-- Prove2me | Theorems.Thm_ULHC_inc_count
-- name    : ULHC.inc_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:57:07.604885+00:00
-- url     : https://prove2.me/theorems/74dc53e1-0f78-404a-bb06-b371a5d29b67
-- title:
--   ULHC: inc count
-- statement:
--   The ULHC construction uses the inc count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L227-L233
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L227-L233

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.inc_count (e : Edge) (y : Pt) :
    (if eR y = e then 1 else 0) + (if eU y = e then 1 else 0) + (if eL y = e then 1 else 0) +
      (if eD y = e then 1 else 0) = (if e.p = y ∨ e.q = y then 1 else 0 : ℕ) := by sorry
