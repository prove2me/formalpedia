-- Prove2me | Theorems.Thm_ULHC_back_down
-- name    : ULHC.back_down
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:20:31.565061+00:00
-- url     : https://prove2.me/theorems/0ab5ec80-a969-4a7f-99d5-d81cdea2b5c0
-- title:
--   ULHC: back down
-- statement:
--   The ULHC construction uses the back down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L148-L159
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L148-L159

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) {c : Pt} {s : Side} {n : ℕ}
include hF
variable (hT : NoTypeIII V F)
include hT

theorem ULHC.back_down (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c)
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) : lat1 (nb c s.opp) s ∈ F := by sorry
