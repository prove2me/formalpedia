-- Prove2me | Theorems.Thm_ULHC_flip_alt_count
-- name    : ULHC.flip_alt_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:54:04.930012+00:00
-- url     : https://prove2.me/theorems/37481ce5-d856-42a1-b7ec-5614891b63c8
-- title:
--   ULHC: flip alt count
-- statement:
--   The ULHC construction uses the flip alt count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Cr2.lean#L54-L70
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Cr2.lean#L54-L70

import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {G : Finset Edge}

theorem ULHC.flip_alt_count (hG : Deg2 V G) {u : Pt} {s : Side} (hu : IsCell V u)
    (l1 : lat1 u s ∈ G) (l2 : lat2 u s ∈ G) (hb : back u s ∉ G) (hf : front u s ∉ G) :
    (Conn G (back1 u s) (back2 u s) → ncomp V (flip G u) = ncomp V G + 1) ∧
      (¬ Conn G (back1 u s) (back2 u s) → ncomp V (flip G u) + 1 = ncomp V G) := by sorry
