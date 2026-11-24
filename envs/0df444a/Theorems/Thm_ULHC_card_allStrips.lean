-- Prove2me | Theorems.Thm_ULHC_card_allStrips
-- name    : ULHC.card_allStrips
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:56:10.358292+00:00
-- url     : https://prove2.me/theorems/a34d0322-e9f0-4a50-9328-8d633de66d81
-- title:
--   ULHC: card all Strips
-- statement:
--   The ULHC construction uses the card all Strips property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Enum.lean#L148-L163
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Enum.lean#L148-L163

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
set_option autoImplicit true
open ULHC
open Finset
variable (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side)
variable {V F c s}
variable (V F)
variable {V F}

theorem ULHC.card_allStrips : (allStrips V F).card ≤ 4 * V.card := by sorry
