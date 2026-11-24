-- Prove2me | Theorems.Thm_ULHC_wD_zero_of_not_mem
-- name    : ULHC.wD_zero_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:55:40.386397+00:00
-- url     : https://prove2.me/theorems/08a3bb64-d41b-44ec-a61e-58a029671d4a
-- title:
--   ULHC: w D zero of not mem
-- statement:
--   The ULHC construction uses the w D zero of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L140-L141
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L140-L141

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}

theorem ULHC.wD_zero_of_not_mem {e : Edge} (h1 : e ∉ F) (h2 : e ∉ H) : wD F H e = 0 := by sorry
