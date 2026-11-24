-- Prove2me | Theorems.Thm_ULHC_notTypeIII_of_corners
-- name    : ULHC.notTypeIII_of_corners
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:33:13.581826+00:00
-- url     : https://prove2.me/theorems/946de712-17cc-44dd-80e7-08ebf1ec2fd4
-- title:
--   ULHC: not Type III of corners
-- statement:
--   The ULHC construction uses the not Type III of corners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L120-L129
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L120-L129

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.notTypeIII_of_corners {V : Finset Pt} {F : Finset Edge} {d : Pt}
    (h : Conn F d (d.1 + 1, d.2) ∧ Conn F d (d.1, d.2 + 1) ∧ Conn F d (d.1 + 1, d.2 + 1)) :
    NotTypeIII V F d := by sorry
