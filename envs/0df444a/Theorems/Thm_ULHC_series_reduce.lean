-- Prove2me | Theorems.Thm_ULHC_series_reduce
-- name    : ULHC.series_reduce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:54:38.960358+00:00
-- url     : https://prove2.me/theorems/c2f19047-2832-4190-8b8d-14b8c902c844
-- title:
--   ULHC: series reduce
-- statement:
--   The ULHC construction uses the series reduce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Stacked.lean#L69-L149
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Stacked.lean#L69-L149

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Stacked
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.series_reduce {A K : Finset Edge} {m1 m2 x y : Pt} {a b c d : Edge}
    (ha : Ends a x m1) (hb : Ends b m1 m2) (hc : Ends c m2 y) (hd : Ends d x y)
    (aA : a ∈ A) (bA : b ∈ A) (cA : c ∈ A) (dK : d ∈ K)
    (hxm2 : x ≠ m2) (hym1 : y ≠ m1)
    (hdeg1 : deg A m1 ≤ 2) (hdeg2 : deg A m2 ≤ 2)
    (hoff : ∀ g ∈ A, ¬ (g.p = m1 ∨ g.q = m1) → ¬ (g.p = m2 ∨ g.q = m2) → g ∈ K)
    (hK : ∀ g ∈ K, g ∈ A ∨ g = d)
    {p q : Pt} (hp1 : p ≠ m1) (hp2 : p ≠ m2) (hq1 : q ≠ m1) (hq2 : q ≠ m2) :
    Conn A p q ↔ Conn K p q := by sorry
