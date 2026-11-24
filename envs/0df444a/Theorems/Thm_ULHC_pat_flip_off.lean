-- Prove2me | Theorems.Thm_ULHC_pat_flip_off
-- name    : ULHC.pat_flip_off
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:18:21.20115+00:00
-- url     : https://prove2.me/theorems/9c3bb46a-e1a2-479e-9bd6-a426879e2414
-- title:
--   ULHC: pat flip off
-- statement:
--   The ULHC construction uses the pat flip off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L25-L30
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L25-L30

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.pat_flip_off {F : Finset Edge} {u : Pt} {w : StripSpec} (h1 : 1 ≤ w.n)
    (hoff : ∀ j < w.n, ∀ x ∈ cellE (cellJ w.c w.s j), x ∉ cellE u) :
    StripPat (flip F u) w.c w.s w.n ↔ StripPat F w.c w.s w.n := by sorry
