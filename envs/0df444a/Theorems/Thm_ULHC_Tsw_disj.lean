-- Prove2me | Theorems.Thm_ULHC_Tsw_disj
-- name    : ULHC.Tsw_disj
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:37:01.058342+00:00
-- url     : https://prove2.me/theorems/3f82076d-5ac8-4fb2-854f-cc08e05de75b
-- title:
--   ULHC: Tsw disj
-- statement:
--   The ULHC construction uses the Tsw disj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L117-L127
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L117-L127

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.Tsw_disj {j j' : ℕ} (hj : j % 2 = 1) (hj' : j' % 2 = 1) (h : j ≠ j') :
    Disjoint (Tsw c s j) (Tsw c s j') := by sorry
