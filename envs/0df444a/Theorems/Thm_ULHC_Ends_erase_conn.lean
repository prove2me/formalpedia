-- Prove2me | Theorems.Thm_ULHC_Ends_erase_conn
-- name    : ULHC.Ends.erase_conn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:35.487878+00:00
-- url     : https://prove2.me/theorems/656bdb45-8947-4b43-b2ce-a5f8f6312874
-- title:
--   Ends: erase conn
-- statement:
--   The Ends construction uses the erase conn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L70-L79
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L70-L79

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
set_option autoImplicit true
open ULHC
open Finset Classical
variable {e : Edge} {u v : Pt}

theorem ULHC.Ends.erase_conn {V : Finset Pt} {F : Finset Edge} (hV : Inside V F) (h : Ends e u v)
    (he : e ∈ F) (heven : ∀ z ∈ V, Conn F u z → Even (deg F z)) : Conn (F.erase e) u v := by sorry
