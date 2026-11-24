-- Prove2me | Theorems.Thm_ULHC_created_iff
-- name    : ULHC.created_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:56:57.166836+00:00
-- url     : https://prove2.me/theorems/40fd69c4-74d4-49fa-a1e6-14e5a1fea7c9
-- title:
--   ULHC: created iff
-- statement:
--   The ULHC construction uses the created iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Created.lean#L119-L277
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Created.lean#L119-L277

import Definitions.Def_ULHC_Reroute
import Definitions.Def_ULHC_Created
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
include hs x0 hconn hF hT hk hcell hpat hsep hT'

theorem ULHC.created_iff {e : Edge} (hE : IsEdge V e) (hfar : ∀ j, e ∉ Tsw c s j) :
    ((∃ B : Finset Edge, (∀ x, IsCell V x → sidesIn B x % 2 = 0) ∧
        (∀ f ∈ B, f ∉ F ∨ f = lat1 (cellJ c s (k + 1)) s ∨ f = lat2 (cellJ c s (k + 1)) s) ∧
        (∀ f ∈ B, f ∉ cellE c) ∧
        (∀ f ∈ B, f ∈ cellE (cellJ c s (k + 1)) →
          f = lat1 (cellJ c s (k + 1)) s ∨ f = lat2 (cellJ c s (k + 1)) s) ∧ e ∈ B) ∧
      ¬ (∃ B : Finset Edge, (∀ x, IsCell V x → sidesIn B x % 2 = 0) ∧ (∀ f ∈ B, f ∉ F) ∧
        (∀ f ∈ B, f ∉ cellE c) ∧ (∀ f ∈ B, f ∉ cellE (cellJ c s (k + 1))) ∧ e ∈ B)) ↔
    (Conn (flipCol F c s (k + 2)) e.p (back1 (cellJ c s (k + 1)) s) ∧
        Conn (flipCol F c s (k + 2)) e.q (front1 (cellJ c s (k + 1)) s)) ∨
      (Conn (flipCol F c s (k + 2)) e.p (front1 (cellJ c s (k + 1)) s) ∧
        Conn (flipCol F c s (k + 2)) e.q (back1 (cellJ c s (k + 1)) s)) := by sorry
