-- Prove2me | Theorems.Thm_ULHC_side1_down
-- name    : ULHC.side1_down
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:00:20.927664+00:00
-- url     : https://prove2.me/theorems/74c8851c-8a9e-4f22-a337-8d6077590801
-- title:
--   ULHC: side1 down
-- statement:
--   The ULHC construction uses the side1 down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearChain.lean#L25-L27
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearChain.lean#L25-L27

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.side1_down (c : Pt) (s : Side) (j : ℕ) :
    nb (nb (cellJ c s (j + 1)) (latA s)) s.opp = nb (cellJ c s j) (latA s) := by sorry
