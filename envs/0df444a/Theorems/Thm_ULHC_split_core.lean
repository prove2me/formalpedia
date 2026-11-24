-- Prove2me | Theorems.Thm_ULHC_split_core
-- name    : ULHC.split_core
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:35:37.927863+00:00
-- url     : https://prove2.me/theorems/0b6ef8e4-bc82-48b3-9b6d-2b317441320c
-- title:
--   ULHC: split core
-- statement:
--   The ULHC construction uses the split core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L404-L422
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L404-L422

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
  {z : Pt} {tf : Side} {m : ℕ} (hz : StripPat F z tf m)
include hs x0 hconn hF hT hk hcell hpat hsep hT' hz
omit hs hconn hz
omit x0

theorem ULHC.split_core {w : Pt} {tw : Side} (hw : IsCell V w) (l1 : lat1 w tw ∈ F)
    (l2 : lat2 w tw ∈ F) (bw : back w tw ∉ F) (fw : front w tw ∉ F)
    (hwe : w ≠ cellJ c s (k + 1)) (hwu : w ≠ nb (cellJ c s (k + 1)) s)
    (hsplit : ¬ Conn (flip F w) (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    False := by sorry
