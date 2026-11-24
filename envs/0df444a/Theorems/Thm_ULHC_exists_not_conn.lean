-- Prove2me | Theorems.Thm_ULHC_exists_not_conn
-- name    : ULHC.exists_not_conn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:37:58.570818+00:00
-- url     : https://prove2.me/theorems/8cc062e1-1e6c-4000-915a-15ae4f256d3c
-- title:
--   ULHC: exists not conn
-- statement:
--   The ULHC construction uses the exists not conn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TheoremA.lean#L154-L165
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TheoremA.lean#L154-L165

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.exists_not_conn {V : Finset Pt} {F : Finset Edge} (h2 : 2 ≤ ncomp V F) :
    ∃ x ∈ V, ∃ y ∈ V, ¬ Conn F x y := by sorry
