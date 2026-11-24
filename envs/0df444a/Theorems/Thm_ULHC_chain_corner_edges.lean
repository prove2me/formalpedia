-- Prove2me | Theorems.Thm_ULHC_chain_corner_edges
-- name    : ULHC.chain_corner_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:04:41.569627+00:00
-- url     : https://prove2.me/theorems/0e7c2b73-b65a-4d62-ba5e-a7e42f7e2174
-- title:
--   ULHC: chain corner edges
-- statement:
--   The ULHC construction uses the chain corner edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L813-L831
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L813-L831

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.chain_corner_edges {F : Finset Edge} {w : StripSpec} (h1 : 1 ≤ w.n)
    (hb : back w.c w.s ∈ F) (hfr : front w.c w.s ∈ F ↔ w.n = 1)
    (hzs : SigFrom F w.c w.s w.n 1) :
    (back w.c w.s ∈ F ∧ ((back w.c w.s).p = back1 w.c w.s ∨ (back w.c w.s).q = back1 w.c w.s) ∧
      back w.c w.s ∈ cellE (cellJ w.c w.s 0)) ∧
    ∃ j < w.n, ∃ x ∈ F, (x.p = front1 w.c w.s ∨ x.q = front1 w.c w.s) ∧
      x ∈ cellE (cellJ w.c w.s j) := by sorry
