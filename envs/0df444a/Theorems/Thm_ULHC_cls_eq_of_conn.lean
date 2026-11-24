-- Prove2me | Theorems.Thm_ULHC_cls_eq_of_conn
-- name    : ULHC.cls_eq_of_conn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:02.669026+00:00
-- url     : https://prove2.me/theorems/b433f26e-6200-4b8d-b7af-bfcb45783551
-- title:
--   ULHC: cls eq of conn
-- statement:
--   The ULHC construction uses the cls eq of conn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L104-L110
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L104-L110

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.cls_eq_of_conn {V : Finset Pt} {F : Finset Edge} {x y : Pt} (h : Conn F x y) :
    cls V F x = cls V F y := by sorry
