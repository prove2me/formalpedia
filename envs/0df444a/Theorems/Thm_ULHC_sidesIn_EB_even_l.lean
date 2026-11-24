-- Prove2me | Theorems.Thm_ULHC_sidesIn_EB_even_l
-- name    : ULHC.sidesIn_EB_even_l
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:41:46.327228+00:00
-- url     : https://prove2.me/theorems/14d53910-f564-4d05-879a-2cfb14c7db85
-- title:
--   ULHC: sides In EB even l
-- statement:
--   The ULHC construction uses the sides In EB even l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L881-L915
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L881-L915

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}

theorem ULHC.sidesIn_EB_even_l (hF : Deg2 V F) (c0 : Pt)
    (hC : ∀ c ∈ chainCells V F c0, NotTypeIII V F c) :
    ∀ c, IsCell V c → sidesIn (EB V F c0) c % 2 = 0 := by sorry
