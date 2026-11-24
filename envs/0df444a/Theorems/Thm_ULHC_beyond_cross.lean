-- Prove2me | Theorems.Thm_ULHC_beyond_cross
-- name    : ULHC.beyond_cross
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:28:40.376557+00:00
-- url     : https://prove2.me/theorems/3b448d49-a0c9-4857-a0e3-467dab03d214
-- title:
--   ULHC: beyond cross
-- statement:
--   The ULHC construction uses the beyond cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L372-L397
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L372-L397

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

theorem ULHC.beyond_cross (ht : tf = latA s ∨ tf = latB s) (hq : z = nb (cellJ c s (k + 1)) s)
    (hm : 2 ≤ m) : False := by sorry
