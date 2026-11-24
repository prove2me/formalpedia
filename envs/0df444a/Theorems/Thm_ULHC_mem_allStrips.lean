-- Prove2me | Theorems.Thm_ULHC_mem_allStrips
-- name    : ULHC.mem_allStrips
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:55:52.803431+00:00
-- url     : https://prove2.me/theorems/7eb1c7c8-6df1-4888-8f4c-e90fe9048ad4
-- title:
--   ULHC: mem all Strips
-- statement:
--   The ULHC construction uses the mem all Strips property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Enum.lean#L134-L146
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Enum.lean#L134-L146

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

theorem ULHC.mem_allStrips {σ : StripSpec} :
    σ ∈ allStrips V F ↔
      1 ≤ σ.n ∧ StripPat F σ.c σ.s σ.n ∧ ∀ j < σ.n, IsCell V (cellJ σ.c σ.s j) := by sorry
