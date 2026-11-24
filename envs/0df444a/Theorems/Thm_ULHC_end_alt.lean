-- Prove2me | Theorems.Thm_ULHC_end_alt
-- name    : ULHC.end_alt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:55:20.687668+00:00
-- url     : https://prove2.me/theorems/f2115812-e9dc-4efc-a824-a347d369a8d1
-- title:
--   ULHC: end alt
-- statement:
--   The ULHC construction uses the end alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CrPath.lean#L104-L115
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CrPath.lean#L104-L115

import Definitions.Def_ULHC_Cr2
import Definitions.Def_ULHC_CrPath
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.end_alt {F : Finset Edge} {σ : StripSpec} (h2 : 2 ≤ σ.n) (he : σ.n % 2 = 0)
    (hp : StripPat F σ.c σ.s σ.n) :
    lat1 (endCell σ) σ.s ∈ F ∧ lat2 (endCell σ) σ.s ∈ F ∧ back (endCell σ) σ.s ∉ F ∧
      front (endCell σ) σ.s ∉ F := by sorry
