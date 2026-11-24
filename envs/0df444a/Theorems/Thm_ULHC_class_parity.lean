-- Prove2me | Theorems.Thm_ULHC_class_parity
-- name    : ULHC.class_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:31.213011+00:00
-- url     : https://prove2.me/theorems/30695c8e-80af-4a65-914c-c29659042947
-- title:
--   ULHC: class parity
-- statement:
--   The ULHC construction uses the class parity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Flip.lean#L34-L50
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Flip.lean#L34-L50

import Definitions.Def_ULHC_Graph
import Definitions.Def_ULHC_Flip
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.class_parity {V : Finset Pt} {G : Finset Edge} (hV : Inside V G) (x : Pt) (S : Finset Pt)
    (h : ∀ z ∈ cls V G x, deg G z = if z ∈ S then 1 else 2) :
    Even ((cls V G x ∩ S).card) := by sorry
