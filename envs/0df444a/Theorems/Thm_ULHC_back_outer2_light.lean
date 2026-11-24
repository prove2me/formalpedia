-- Prove2me | Theorems.Thm_ULHC_back_outer2_light
-- name    : ULHC.back_outer2_light
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:25:14.261674+00:00
-- url     : https://prove2.me/theorems/febc5c42-8046-46d5-8f0a-5da9c242609b
-- title:
--   ULHC: back outer2 light
-- statement:
--   The ULHC construction uses the back outer2 light property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L216-L256
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L216-L256

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

theorem ULHC.back_outer2_light (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c)
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) : back (nb c (latB s)) s ∉ F := by sorry
