-- Prove2me | Theorems.Thm_ULHC_touch_outcomeW
-- name    : ULHC.touch_outcomeW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:56:51.643938+00:00
-- url     : https://prove2.me/theorems/bef028de-4254-42ce-a552-4a09e9dad7a3
-- title:
--   ULHC: touch outcome W
-- statement:
--   The ULHC construction uses the touch outcome W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L200-L240
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L200-L240

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
  {z : Pt} {tf : Side} {m i0 : ℕ} (hzw : SigFrom F z tf m i0)
include hs x0 hconn hF hT hk hcell hpat hsep hT' hzw
omit hs x0 hconn

theorem ULHC.touch_outcomeW {i j : ℕ} (hi0 : i0 ≤ i) (hi : i < m) (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE (cellJ z tf i)) (hx2 : x ∈ cellE (cellJ c s j)) :
    (∃ i', i ≤ i' ∧ i' < m ∧ cellJ z tf i' = cellJ c s (k + 1)) ∨
      (∃ i', i ≤ i' ∧ i' < m ∧ cellJ z tf i' = nb (cellJ c s (k + 1)) s) ∨
      (tf = s.opp ∧ ∃ ie, i ≤ ie ∧ ie < m ∧ ie % 2 = 0 ∧
        (cellJ z tf ie = nb c (latA s) ∨ cellJ z tf ie = nb c (latB s))) := by sorry
