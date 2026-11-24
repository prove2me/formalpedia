-- Prove2me | Theorems.Thm_ULHC_deg_zero_of_not_mem
-- name    : ULHC.deg_zero_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:55:24.102189+00:00
-- url     : https://prove2.me/theorems/c05a844d-0627-4ede-9c81-9d2be60f6872
-- title:
--   ULHC: deg zero of not mem
-- statement:
--   The ULHC construction uses the deg zero of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L65-L75
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L65-L75

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.deg_zero_of_not_mem {V : Finset Pt} {d : Pt → ℕ} {F : Finset Edge}
    (hF : IsFactor V d F) {p : Pt} (hp : p ∉ V) : deg F p = 0 := by sorry
