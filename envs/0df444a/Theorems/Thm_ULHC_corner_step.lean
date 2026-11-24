-- Prove2me | Theorems.Thm_ULHC_corner_step
-- name    : ULHC.corner_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:42:34.183278+00:00
-- url     : https://prove2.me/theorems/2db09386-2058-42dc-bd88-5575c46d50e9
-- title:
--   ULHC: corner step
-- statement:
--   The ULHC construction uses the corner step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L232-L253
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L232-L253

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.corner_step {F : Finset Edge} {K : Finset Pt} {x : Pt} {e1 e2 : Edge} {a1 b1 a2 b2 : Pt}
    (h1 : Ends e1 a1 b1) (h2 : Ends e2 a2 b2) (he1 : e1 ∈ F) (he2 : e2 ∈ F) (hne : e1 ≠ e2)
    (hd : deg F x = 2) (i1 : x = a1 ∨ x = b1) (i2 : x = a2 ∨ x = b2)
    (k1 : a1 ∈ K ∧ b1 ∈ K) (k2 : a2 ∈ K ∧ b2 ∈ K) : ∀ y, Adj F x y → y ∈ K := by sorry
