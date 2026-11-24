-- Prove2me | Theorems.Thm_ULHC_flipCol_off
-- name    : ULHC.flipCol_off
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:55:09.438803+00:00
-- url     : https://prove2.me/theorems/634a9e1e-849b-400c-89f9-4bb9aa728668
-- title:
--   ULHC: flip Col off
-- statement:
--   The ULHC construction uses the flip Col off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CrPath.lean#L55-L74
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CrPath.lean#L55-L74

import Definitions.Def_ULHC_Cr2
import Definitions.Def_ULHC_CrPath
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.flipCol_off (G : Finset Edge) (c : Pt) (s : Side) (n : ℕ) {e : Edge}
    (h : ∀ i, i + 1 < n + 1 → e ∉ cellE (cellJ c s i)) :
    e ∈ flipCol G c s (n + 1) ↔ e ∈ flip G (cellJ c s n) := by sorry
