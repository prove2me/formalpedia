-- Prove2me | Theorems.Thm_ULHC_start_frame
-- name    : ULHC.start_frame
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:05:28.046454+00:00
-- url     : https://prove2.me/theorems/7347c680-01a5-4a25-972f-947791ea544b
-- title:
--   ULHC: start frame
-- statement:
--   The ULHC construction uses the start frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L157-L171
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L157-L171

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.start_frame {F : Finset Edge} {d : Pt} {tf : Side} (s : Side) (hb : back d tf ∈ F)
    (hxl : (lat1 d tf ∈ F ∧ lat2 d tf ∉ F) ∨ (lat2 d tf ∈ F ∧ lat1 d tf ∉ F)) :
    ((tf = s ∨ tf = s.opp) ∧ (lat1 d s ∈ F ↔ lat2 d s ∉ F)) ∨
      ((tf = latA s ∨ tf = latB s) ∧ (lat1 d s ∈ F ∨ lat2 d s ∈ F) ∧
        (back d s ∈ F ↔ front d s ∉ F)) := by sorry
