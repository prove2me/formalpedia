-- Prove2me | Theorems.Thm_ULHC_D_flip_sink
-- name    : ULHC.D_flip_sink
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:29.522672+00:00
-- url     : https://prove2.me/theorems/b7f0284a-e9e5-4c2a-b4b5-bc5e103dfdca
-- title:
--   ULHC: D flip sink
-- statement:
--   The ULHC construction uses the D flip sink property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L278-L288
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L278-L288

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.D_flip_sink {F H : Finset Edge} {c : Pt} (h : Sink F c) (x : Pt) :
    D (flip F c) H x = D F H x - (if x = c then 2 else 0) := by sorry
