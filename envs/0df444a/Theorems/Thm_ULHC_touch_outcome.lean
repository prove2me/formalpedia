-- Prove2me | Theorems.Thm_ULHC_touch_outcome
-- name    : ULHC.touch_outcome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:35:28.813883+00:00
-- url     : https://prove2.me/theorems/c82b80d5-74b5-40e2-a78f-b1dc198d6c6c
-- title:
--   ULHC: touch outcome
-- statement:
--   The ULHC construction uses the touch outcome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L259-L299
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L259-L299

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
omit hs hconn
omit x0

theorem ULHC.touch_outcome {i j : ℕ} (hi : i < m) (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE (cellJ z tf i)) (hx2 : x ∈ cellE (cellJ c s j)) :
    (∃ i' < m, cellJ z tf i' = cellJ c s (k + 1)) ∨
      (∃ i' < m, cellJ z tf i' = nb (cellJ c s (k + 1)) s) ∨
      (tf = s.opp ∧ ∃ i0 < m, i0 % 2 = 0 ∧
        (cellJ z tf i0 = nb c (latA s) ∨ cellJ z tf i0 = nb c (latB s))) := by sorry
