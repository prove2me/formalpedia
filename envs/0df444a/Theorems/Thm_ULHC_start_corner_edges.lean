-- Prove2me | Theorems.Thm_ULHC_start_corner_edges
-- name    : ULHC.start_corner_edges
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:03:20.108406+00:00
-- url     : https://prove2.me/theorems/b62d3ae5-2614-4ddb-a95c-c3c431523a57
-- title:
--   ULHC: start corner edges
-- statement:
--   The ULHC construction uses the start corner edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L34-L51
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L34-L51

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.start_corner_edges {F : Finset Edge} {w : StripSpec} (hp : StripPat F w.c w.s w.n)
    (h1 : 1 ≤ w.n) :
    (back w.c w.s ∈ F ∧ ((back w.c w.s).p = back1 w.c w.s ∨ (back w.c w.s).q = back1 w.c w.s) ∧
      back w.c w.s ∈ cellE (cellJ w.c w.s 0)) ∧
    ∃ j < w.n, ∃ x ∈ F, (x.p = front1 w.c w.s ∨ x.q = front1 w.c w.s) ∧
      x ∈ cellE (cellJ w.c w.s j) := by sorry
