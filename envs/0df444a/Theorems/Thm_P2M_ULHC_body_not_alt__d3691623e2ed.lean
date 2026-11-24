-- Prove2me | Theorems.Thm_P2M_ULHC_body_not_alt__d3691623e2ed
-- name    : P2M_ULHC_body_not_alt__d3691623e2ed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:23:01.934818+00:00
-- url     : https://prove2.me/theorems/dc46b6f7-c3ba-4baf-a927-517d1a0d8ff9
-- title:
--   P2 M ULHC body not alt  d3691623e2ed: P2 M ULHC body not alt  d3691623e2ed
-- statement:
--   The P2 M ULHC body not alt  d3691623e2ed construction uses the P2 M ULHC body not alt  d3691623e2ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L173-L179
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L173-L179

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset

theorem P2M_ULHC_body_not_alt__d3691623e2ed {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} (hk : k % 2 = 0)
    (hpat : StripPat F c s (k + 2)) {j : ℕ} (hj : j ≤ k) {tw : Side}
    (l1 : lat1 (cellJ c s j) tw ∈ F) (l2 : lat2 (cellJ c s j) tw ∈ F)
    (bw : back (cellJ c s j) tw ∉ F) (fw : front (cellJ c s j) tw ∉ F) : False := by sorry

alias «ULHC».«body_not_alt'» := P2M_ULHC_body_not_alt__d3691623e2ed
