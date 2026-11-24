-- Prove2me | Theorems.Thm_ULHC_reroute_fwd_rung
-- name    : ULHC.reroute_fwd_rung
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:49:50.880623+00:00
-- url     : https://prove2.me/theorems/5c50f9ba-0e02-41f6-9da4-029872101cb0
-- title:
--   ULHC: reroute fwd rung
-- statement:
--   The ULHC construction uses the reroute fwd rung property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L509-L721
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L509-L721

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hk : k % 2 = 0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hpat : StripPat F c s (k + 2))
include hF hk hcell hpat

theorem ULHC.reroute_fwd_rung {B : Finset Edge} (heven : ∀ x, IsCell V x → sidesIn B x % 2 = 0)
    (hlight0 : ∀ e ∈ B, e ∉ F ∨ e = lat1 (cellJ c s (k + 1)) s ∨ e = lat2 (cellJ c s (k + 1)) s)
    (h0 : ∀ e ∈ B, e ∉ cellE c)
    (hu : ∀ e ∈ B, e ∈ cellE (cellJ c s (k + 1)) →
      e = lat1 (cellJ c s (k + 1)) s ∨ e = lat2 (cellJ c s (k + 1)) s) :
    ∃ B' : Finset Edge, (∀ x, IsCell V x → sidesIn B' x % 2 = 0) ∧
      (∀ e ∈ B', e ∉ flipCol F c s (k + 2)) ∧
      (∀ e ∈ B', e ∉ cellE c ∧ (e ∈ cellE (cellJ c s (k + 1)) →
        e = lat1 (cellJ c s (k + 1)) s ∨ e = lat2 (cellJ c s (k + 1)) s)) ∧
      (∀ e, (∀ j, e ∉ Tsw c s j) → (e ∈ B' ↔ e ∈ B)) := by sorry
