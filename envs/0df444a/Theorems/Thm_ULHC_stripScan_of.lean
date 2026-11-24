-- Prove2me | Theorems.Thm_ULHC_stripScan_of
-- name    : ULHC.stripScan_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:51:09.708902+00:00
-- url     : https://prove2.me/theorems/6d547a69-a130-4d87-af4e-a8b10767650c
-- title:
--   ULHC: strip Scan of
-- statement:
--   The ULHC construction uses the strip Scan of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Enum.lean#L79-L93
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Enum.lean#L79-L93

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
set_option autoImplicit true
open ULHC
open Finset
variable (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side)
variable {V F c s}

theorem ULHC.stripScan_of {n : ℕ}
    (hn : ∀ i < n, IsCell V (cellJ c s i) ∧ LatOK F c s i ∧
      (front (cellJ c s i) s ∈ F ↔ (i % 2 = 1 ↔ i + 1 < n))) :
    ∀ k j, j < n → n ≤ j + k → stripScan V F c s k j = some n := by sorry
