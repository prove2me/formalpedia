-- Prove2me | Theorems.Thm_P2M_ULHC_alt_corners_conn__04780e54d852
-- name    : P2M_ULHC_alt_corners_conn__04780e54d852
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:24:15.62914+00:00
-- url     : https://prove2.me/theorems/669237ce-1896-47ff-ab3c-89cb47743e33
-- title:
--   P2 M ULHC alt corners conn  04780e54d852: P2 M ULHC alt corners conn  04780e54d852
-- statement:
--   The P2 M ULHC alt corners conn  04780e54d852 construction uses the P2 M ULHC alt corners conn  04780e54d852 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L211-L225
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L211-L225

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
set_option autoImplicit true
open ULHC
open Finset Classical

theorem P2M_ULHC_alt_corners_conn__04780e54d852 {V : Finset Pt} {F : Finset Edge} {r : Pt} (hT : NotTypeIII V F r)
    (ha : Alt F r) :
    Conn F r (r.1 + 1, r.2) ∧ Conn F r (r.1, r.2 + 1) ∧ Conn F r (r.1 + 1, r.2 + 1) := by sorry

alias «ULHC».«alt_corners_conn'» := P2M_ULHC_alt_corners_conn__04780e54d852
