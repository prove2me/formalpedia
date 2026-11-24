-- Prove2me | Theorems.Thm_ULHC_alt_touch
-- name    : ULHC.alt_touch
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:28:36.646024+00:00
-- url     : https://prove2.me/theorems/55d3dd33-0356-4aa7-9d9a-5708ed093ddf
-- title:
--   ULHC: alt touch
-- statement:
--   The ULHC construction uses the alt touch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L315-L365
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L315-L365

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
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
omit hs hconn hT' hz
omit x0

theorem ULHC.alt_touch {w : Pt} {tw : Side} (l1 : lat1 w tw ∈ F) (l2 : lat2 w tw ∈ F)
    (bw : back w tw ∉ F) (fw : front w tw ∉ F) {j : ℕ} (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE w) (hx2 : x ∈ cellE (cellJ c s j)) :
    w = cellJ c s (k + 1) ∨ w = nb (cellJ c s (k + 1)) s := by sorry
