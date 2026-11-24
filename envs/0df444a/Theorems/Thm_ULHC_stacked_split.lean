-- Prove2me | Theorems.Thm_ULHC_stacked_split
-- name    : ULHC.stacked_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:26:28.58017+00:00
-- url     : https://prove2.me/theorems/329cfce3-8bc4-4f74-ab92-f95c0fc83208
-- title:
--   ULHC: stacked split
-- statement:
--   The ULHC construction uses the stacked split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Stacked.lean#L223-L348
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Stacked.lean#L223-L348

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Stacked
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.stacked_split {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) {e : Pt} {s : Side}
    (he : IsCell V e) (hu : IsCell V (nb e s))
    (el1 : lat1 e s ∈ F) (el2 : lat2 e s ∈ F) (eb : back e s ∉ F) (ef : front e s ∉ F)
    (ul1 : lat1 (nb e s) s ∈ F) (ul2 : lat2 (nb e s) s ∈ F) (uf : front (nb e s) s ∉ F)
    {p q : Pt} (hp1 : p ≠ front1 e s) (hp2 : p ≠ front2 e s)
    (hq1 : q ≠ front1 e s) (hq2 : q ≠ front2 e s) :
    Conn (flip F e) p q ↔ Conn (flip F (nb e s)) p q := by sorry
