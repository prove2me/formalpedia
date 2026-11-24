-- Prove2me | Theorems.Thm_ULHC_osi_far
-- name    : ULHC.osi_far
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:51:05.082323+00:00
-- url     : https://prove2.me/theorems/61627c61-7421-420a-a5d6-1095d761846c
-- title:
--   ULHC: osi far
-- statement:
--   The ULHC construction uses the osi far property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Cr2.lean#L240-L254
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Cr2.lean#L240-L254

import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hG : Deg2 V G) (hk : k % 2 = 0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hpat : StripPat G c s (k + 2)) (hsep : ¬ Conn G (back1 c s) (front1 c s))
  (hsame : Conn G (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s))
  (hT' : NoTypeIII V (flipCol G c s (k + 2)))
include hG hk hcell hpat hsep hsame hT'

theorem ULHC.osi_far {u : Pt} {tf : Side} (hu : IsCell V u)
    (lu1 : lat1 u tf ∈ G) (lu2 : lat2 u tf ∈ G) (bu : back u tf ∉ G) (fu : front u tf ∉ G)
    (hsu : Conn G (back1 u tf) (back2 u tf))
    (hfar : ∀ j ≤ k + 1, ∀ e ∈ cellE u, e ∉ cellE (cellJ c s j))
    (hmu1 : ¬ IsMid c s k (back1 u tf)) (hmu2 : ¬ IsMid c s k (back2 u tf))
    {x y : Pt} (hxy : Conn G x y) (hsplit : ¬ Conn (flip G u) x y)
    (hx : ¬ IsMid c s k x) (hy : ¬ IsMid c s k y) :
    (Conn (flipCol G c s (k + 2)) x y ∧ ¬ Conn (flip (flipCol G c s (k + 2)) u) x y) ∨
      ¬ Conn (flip G (cellJ c s (k + 1))) x y := by sorry
