-- Prove2me | Theorems.Thm_ULHC_not_conn_swap
-- name    : ULHC.not_conn_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:57:55.550292+00:00
-- url     : https://prove2.me/theorems/de946527-fb40-4e0a-8fb1-df3929a63c3b
-- title:
--   ULHC: not conn swap
-- statement:
--   The ULHC construction uses the not conn swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Strip.lean#L150-L151
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Strip.lean#L150-L151

import Definitions.Def_ULHC_Iso
import Definitions.Def_ULHC_Strip
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.not_conn_swap {G : Finset Edge} {u v w : Pt} (huw : Conn G u w) (h : ¬ Conn G v u) :
    ¬ Conn G v w := by sorry
