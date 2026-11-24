-- Prove2me | Theorems.Thm_ULHC_reroute_back
-- name    : ULHC.reroute_back
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:49:56.740797+00:00
-- url     : https://prove2.me/theorems/065d2b4b-6bd5-4ba1-9d7c-49b655ba14c3
-- title:
--   ULHC: reroute back
-- statement:
--   The ULHC construction uses the reroute back property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L170-L330
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L170-L330

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hk : k % 2 = 0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hpat : StripPat F c s (k + 2))
include hF hk hcell hpat

theorem ULHC.reroute_back {B : Finset Edge} (heven : ∀ x, IsCell V x → sidesIn B x % 2 = 0)
    (hlight : ∀ e ∈ B, e ∉ flipCol F c s (k + 2)) (h0 : ∀ e ∈ B, e ∉ cellE c)
    (hu : ∀ e ∈ B, e ∉ cellE (cellJ c s (k + 1))) :
    ∃ B' : Finset Edge, (∀ x, IsCell V x → sidesIn B' x % 2 = 0) ∧ (∀ e ∈ B', e ∉ F) ∧
      (∀ e ∈ B', e ∉ cellE c ∧ e ∉ cellE (cellJ c s (k + 1))) ∧
      (∀ e, (∀ j, e ∉ Tsw c s j) → (e ∈ B' ↔ e ∈ B)) := by sorry
