-- Prove2me | Theorems.Thm_ULHC_chain_border
-- name    : ULHC.chain_border
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:41:39.302345+00:00
-- url     : https://prove2.me/theorems/e36eece9-b373-4e95-a154-9c20d6947dcb
-- title:
--   ULHC: chain border
-- statement:
--   The ULHC construction uses the chain border property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L868-L875
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L868-L875

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}

theorem ULHC.chain_border (hs : Solid V) (hF : Deg2 V F) (hT : NoTypeIII V F) (x0 : Pt)
    (hconn : ∀ z ∈ V, Conn (GE V) x0 z) (c0 : Pt) :
    ∃ P : Finset Pt, Border V F P ∧ ∀ e, IsEdge V e → (Cut P e ↔ e ∈ EB V F c0) := by sorry
