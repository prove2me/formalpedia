-- Prove2me | Theorems.Thm_ULHC_sidesIn_biUnion_even
-- name    : ULHC.sidesIn_biUnion_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:37:29.531078+00:00
-- url     : https://prove2.me/theorems/4050401e-4e77-4377-8e95-61142b2fdca8
-- title:
--   ULHC: sides In bi Union even
-- statement:
--   The ULHC construction uses the sides In bi Union even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L137-L155
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L137-L155

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.sidesIn_biUnion_even (J : Finset ℕ) (f : ℕ → Finset Edge)
    (hd : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (f i) (f j))
    (he : ∀ j ∈ J, ∀ x, sidesIn (f j) x % 2 = 0) (x : Pt) :
    sidesIn (J.biUnion f) x % 2 = 0 := by sorry
