-- Prove2me | Theorems.Thm_ULHC_rev_valid
-- name    : ULHC.rev_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:57:52.776928+00:00
-- url     : https://prove2.me/theorems/7a30ce0f-1417-4c31-910c-21bb21258352
-- title:
--   ULHC: rev valid
-- statement:
--   The ULHC construction uses the rev valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reverse.lean#L87-L93
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reverse.lean#L87-L93

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_Reverse
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
include hs x0 hconn hF hT hk hcell hpat hsep hT'
omit hs x0 hconn hT'

theorem ULHC.rev_valid :
    ValidStrip V (flipCol F c s (k + 2)) ⟨cellJ c s (k + 1), s.opp, k + 2⟩ := by sorry
