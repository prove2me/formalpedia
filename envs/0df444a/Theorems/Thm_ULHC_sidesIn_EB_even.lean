-- Prove2me | Theorems.Thm_ULHC_sidesIn_EB_even
-- name    : ULHC.sidesIn_EB_even
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:41:29.249655+00:00
-- url     : https://prove2.me/theorems/ec33acb8-1fa0-4c2e-87f9-bfc52d1ea8c4
-- title:
--   ULHC: sides In EB even
-- statement:
--   The ULHC construction uses the sides In EB even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L833-L862
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L833-L862

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}

theorem ULHC.sidesIn_EB_even (hF : Deg2 V F) (hT : NoTypeIII V F) (c0 : Pt) :
    ∀ c, IsCell V c → sidesIn (EB V F c0) c % 2 = 0 := by sorry
