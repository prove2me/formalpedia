-- Prove2me | Theorems.Thm_ULHC_rot_supp_of
-- name    : ULHC.rot_supp_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:43.116358+00:00
-- url     : https://prove2.me/theorems/9402da5d-81ff-4be8-b276-0bb8241f79c8
-- title:
--   ULHC: rot supp of
-- statement:
--   The ULHC construction uses the rot supp of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Planar.lean#L80-L91
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Planar.lean#L80-L91

import Definitions.Def_ULHC_Conn
import Definitions.Def_ULHC_Planar
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.rot_supp_of {f : Edge → ℤ} {L : List Pt} (h : ∀ e, f e ≠ 0 → e.p ∈ L) :
    Supp (edgesAt L) (rot f) := by sorry
