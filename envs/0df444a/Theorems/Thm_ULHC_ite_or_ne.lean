-- Prove2me | Theorems.Thm_ULHC_ite_or_ne
-- name    : ULHC.ite_or_ne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:49:30.787721+00:00
-- url     : https://prove2.me/theorems/e548b2d4-d705-4466-a309-26af4aea2b8d
-- title:
--   ULHC: ite or ne
-- statement:
--   The ULHC construction uses the ite or ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L54-L58
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L54-L58

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.ite_or_ne {x A B : Pt} (h : A ≠ B) :
    (if x = A ∨ x = B then 1 else 0 : ℕ) = (if x = A then 1 else 0) + (if x = B then 1 else 0) := by sorry
