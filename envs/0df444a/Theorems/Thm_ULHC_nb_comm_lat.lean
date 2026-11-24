-- Prove2me | Theorems.Thm_ULHC_nb_comm_lat
-- name    : ULHC.nb_comm_lat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:33:40.238811+00:00
-- url     : https://prove2.me/theorems/e1ff16de-e605-4593-b27b-8556da8c66ca
-- title:
--   ULHC: nb comm lat
-- statement:
--   The ULHC construction uses the nb comm lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L64-L68
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L64-L68

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.nb_comm_lat (j : ℕ) :
    nb (nb (cellJ c s j) (latA s)) s = nb (cellJ c s (j + 1)) (latA s) ∧
      nb (nb (cellJ c s j) (latB s)) s = nb (cellJ c s (j + 1)) (latB s) := by sorry
