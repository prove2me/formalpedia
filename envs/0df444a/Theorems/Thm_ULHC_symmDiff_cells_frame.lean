-- Prove2me | Theorems.Thm_ULHC_symmDiff_cells_frame
-- name    : ULHC.symmDiff_cells_frame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:47:22.47332+00:00
-- url     : https://prove2.me/theorems/76cf1594-22ad-4404-8c70-8df45d0b5fd3
-- title:
--   ULHC: symm Diff cells frame
-- statement:
--   The ULHC construction uses the symm Diff cells frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L223-L237
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L223-L237

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.symmDiff_cells_frame {f x1 x2 x3 y1 y2 y3 : Edge} {E1 E2 : Finset Edge}
    (hE1 : E1 = {f, y1, y2, y3}) (hE2 : E2 = {x1, f, x2, x3})
    (hx : ∀ x ∈ ({x1, x2, x3} : Finset Edge), x ∉ E1)
    (hy : ∀ y ∈ ({y1, y2, y3} : Finset Edge), y ∉ E2) :
    symmDiff E1 E2 = {x1, x2, x3, y1, y2, y3} := by sorry
