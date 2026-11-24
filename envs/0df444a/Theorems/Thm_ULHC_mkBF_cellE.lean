-- Prove2me | Theorems.Thm_ULHC_mkBF_cellE
-- name    : ULHC.mkBF_cellE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:33:36.8825+00:00
-- url     : https://prove2.me/theorems/6bde9162-baec-4f6c-b129-25a2deb74108
-- title:
--   ULHC: mk BF cell E
-- statement:
--   The ULHC construction uses the mk BF cell E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L150-L152
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L150-L152

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.mkBF_cellE (c : Pt) (s : Side) :
    cellE c = {(mkBF c s).e1, (mkBF c s).e2, (mkBF c s).l1, (mkBF c s).l2} := by sorry
