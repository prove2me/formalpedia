-- Prove2me | Theorems.Thm_ULHC_beside_end2
-- name    : ULHC.beside_end2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:58:07.281982+00:00
-- url     : https://prove2.me/theorems/df4a2421-b797-41d8-983f-329c14b8fb34
-- title:
--   ULHC: beside end2
-- statement:
--   The ULHC construction uses the beside end2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L342-L378
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L342-L378

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hs x0 hconn hF hT hk hcell hpat hsep
omit hs x0 hconn

theorem ULHC.beside_end2 (hb : outer2 (cellJ c s k) s ∈ F) (hf : outer2 (cellJ c s (k + 1)) s ∈ F)
    (hl : lat2 (nb (cellJ c s (k + 1)) (latB s)) s ∉ F) :
    ¬ NoTypeIII V (flipCol F c s (k + 2)) := by sorry
