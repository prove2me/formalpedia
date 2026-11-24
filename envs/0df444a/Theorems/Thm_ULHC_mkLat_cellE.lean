-- Prove2me | Theorems.Thm_ULHC_mkLat_cellE
-- name    : ULHC.mkLat_cellE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:10.034798+00:00
-- url     : https://prove2.me/theorems/9747e9ef-874d-4921-bba7-ec87fcde9101
-- title:
--   ULHC: mk Lat cell E
-- statement:
--   The ULHC construction uses the mk Lat cell E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L154-L156
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L154-L156

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.mkLat_cellE (c : Pt) (s : Side) :
    cellE c = {(mkLat c s).e1, (mkLat c s).e2, (mkLat c s).l1, (mkLat c s).l2} := by sorry
