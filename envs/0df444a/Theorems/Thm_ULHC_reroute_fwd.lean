-- Prove2me | Theorems.Thm_ULHC_reroute_fwd
-- name    : ULHC.reroute_fwd
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:49:48.503426+00:00
-- url     : https://prove2.me/theorems/b0508e32-6b50-4ecc-bc0c-92a3cc01227c
-- title:
--   ULHC: reroute fwd
-- statement:
--   The ULHC construction uses the reroute fwd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L334-L505
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L334-L505

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hk : k % 2 = 0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hpat : StripPat F c s (k + 2))
include hF hk hcell hpat

theorem ULHC.reroute_fwd {B : Finset Edge} (heven : ∀ x, IsCell V x → sidesIn B x % 2 = 0)
    (hlight : ∀ e ∈ B, e ∉ F) (h0 : ∀ e ∈ B, e ∉ cellE c)
    (hu : ∀ e ∈ B, e ∉ cellE (cellJ c s (k + 1))) :
    ∃ B' : Finset Edge, (∀ x, IsCell V x → sidesIn B' x % 2 = 0) ∧
      (∀ e ∈ B', e ∉ flipCol F c s (k + 2)) ∧
      (∀ e ∈ B', e ∉ cellE c ∧ e ∉ cellE (cellJ c s (k + 1))) ∧
      (∀ e, (∀ j, e ∉ Tsw c s j) → (e ∈ B' ↔ e ∈ B)) := by sorry
