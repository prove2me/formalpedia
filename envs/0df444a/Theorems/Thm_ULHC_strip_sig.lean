-- Prove2me | Theorems.Thm_ULHC_strip_sig
-- name    : ULHC.strip_sig
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:58:22.74038+00:00
-- url     : https://prove2.me/theorems/c36904c8-9c66-4fec-8849-b16e109ef210
-- title:
--   ULHC: strip sig
-- statement:
--   The ULHC construction uses the strip sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L56-L65
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L56-L65

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.strip_sig {F : Finset Edge} {z : Pt} {tf : Side} {m i : ℕ} (hp : StripPat F z tf m)
    (hi : i < m) :
    (lat1 (cellJ z tf i) tf ∈ F ↔ i % 2 = 1) ∧ (lat2 (cellJ z tf i) tf ∈ F ↔ i % 2 = 1) ∧
      (back (cellJ z tf i) tf ∈ F ↔ i % 2 = 0) ∧
      (front (cellJ z tf i) tf ∈ F ↔ (i % 2 = 1 ↔ i + 1 < m)) := by sorry
