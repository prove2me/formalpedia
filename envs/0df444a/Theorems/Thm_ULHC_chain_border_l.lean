-- Prove2me | Theorems.Thm_ULHC_chain_border_l
-- name    : ULHC.chain_border_l
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:41:59.903716+00:00
-- url     : https://prove2.me/theorems/889301b0-6e84-4669-aa0b-ba9c26b1a812
-- title:
--   ULHC: chain border l
-- statement:
--   The ULHC construction uses the chain border l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L919-L927
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L919-L927

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}

theorem ULHC.chain_border_l (hs : Solid V) (hF : Deg2 V F) (x0 : Pt)
    (hconn : ∀ z ∈ V, Conn (GE V) x0 z) (c0 : Pt)
    (hC : ∀ c ∈ chainCells V F c0, NotTypeIII V F c) :
    ∃ P : Finset Pt, Border V F P ∧ ∀ e, IsEdge V e → (Cut P e ↔ e ∈ EB V F c0) := by sorry
