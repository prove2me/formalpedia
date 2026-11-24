-- Prove2me | Theorems.Thm_ULHC_start_side_sep
-- name    : ULHC.start_side_sep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:24:59.979986+00:00
-- url     : https://prove2.me/theorems/bea67286-4e65-477c-a259-1febed345c21
-- title:
--   ULHC: start side sep
-- statement:
--   The ULHC construction uses the start side sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L187-L212
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L187-L212

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

theorem ULHC.start_side_sep (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c)
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hfar : lat1 (nb c (latA s)) s ∉ F) :
    ¬ Conn F (back1 (nb c (latA s)) s) (front1 (nb c (latA s)) s) := by sorry
