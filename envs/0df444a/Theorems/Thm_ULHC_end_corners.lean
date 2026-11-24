-- Prove2me | Theorems.Thm_ULHC_end_corners
-- name    : ULHC.end_corners
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:37:16.591043+00:00
-- url     : https://prove2.me/theorems/874e315c-3db1-4019-90c9-3cb997b2ee5b
-- title:
--   ULHC: end corners
-- statement:
--   The ULHC construction uses the end corners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Created.lean#L91-L115
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Created.lean#L91-L115

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
omit hs x0 hconn hT'

theorem ULHC.end_corners :
    Conn (flipCol F c s (k + 2)) (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s) ∧
      Conn (flipCol F c s (k + 2)) (front1 (cellJ c s (k + 1)) s)
        (front2 (cellJ c s (k + 1)) s) ∧
      ¬ Conn (flipCol F c s (k + 2)) (back1 (cellJ c s (k + 1)) s)
        (front1 (cellJ c s (k + 1)) s) := by sorry
