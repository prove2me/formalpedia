-- Prove2me | Theorems.Thm_ULHC_alt_corners_conn
-- name    : ULHC.alt_corners_conn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:22:50.537776+00:00
-- url     : https://prove2.me/theorems/93d87252-cc99-4501-a1b9-4ca0a85b5c89
-- title:
--   ULHC: alt corners conn
-- statement:
--   The ULHC construction uses the alt corners conn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L227-L230
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L227-L230

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.alt_corners_conn {V : Finset Pt} {F : Finset Edge} (hT : NoTypeIII V F) {r : Pt}
    (hr : IsCell V r) (ha : Alt F r) :
    Conn F r (r.1 + 1, r.2) ∧ Conn F r (r.1, r.2 + 1) ∧ Conn F r (r.1 + 1, r.2 + 1) := by sorry
