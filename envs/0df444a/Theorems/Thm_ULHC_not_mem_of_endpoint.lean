-- Prove2me | Theorems.Thm_ULHC_not_mem_of_endpoint
-- name    : ULHC.not_mem_of_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:55:50.983249+00:00
-- url     : https://prove2.me/theorems/dc42fa05-6f23-4b3f-b93d-aadab67fb3dd
-- title:
--   ULHC: not mem of endpoint
-- statement:
--   The ULHC construction uses the not mem of endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L148-L152
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L148-L152

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}

theorem ULHC.not_mem_of_endpoint {G : Finset Edge} {d' : Pt → ℕ} (hG : IsFactor V d' G)
    {e : Edge} {a : Pt} (ha : a ∉ V) (h : e.p = a ∨ e.q = a) : e ∉ G := by sorry
