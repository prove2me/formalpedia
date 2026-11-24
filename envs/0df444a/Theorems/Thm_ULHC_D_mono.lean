-- Prove2me | Theorems.Thm_ULHC_D_mono
-- name    : ULHC.D_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:41:10.463687+00:00
-- url     : https://prove2.me/theorems/47bbd4dd-2b22-462d-ba50-a6c77841c3ea
-- title:
--   ULHC: D mono
-- statement:
--   The ULHC construction uses the D mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean#L36-L41
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean#L36-L41

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F H : Finset Edge} (hF : Deg2 V F) (hH : Deg2 V H)
include hF hH

theorem ULHC.D_mono (o : Bool) (c : Pt) (s : Side) (h : outArc F c s = o) :
    if o then D F H c ≤ D F H (nb c s) else D F H (nb c s) ≤ D F H c := by sorry
