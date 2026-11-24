-- Prove2me | Theorems.Thm_ULHC_split_end_t3
-- name    : ULHC.split_end_t3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:53:52.574483+00:00
-- url     : https://prove2.me/theorems/684b99e2-e7ff-4465-9aba-9780bc958c01
-- title:
--   ULHC: split end t3
-- statement:
--   The ULHC construction uses the split end t3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L386-L423
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L386-L423

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_APair_flip

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

theorem ULHC.split_end_t3 {w : Pt} {tw : Side} (hw : IsCell V w)
    (l1 : lat1 w tw ∈ F) (l2 : lat2 w tw ∈ F) (bw : back w tw ∉ F) (fw : front w tw ∉ F)
    (hdisj : ∀ j < k + 2, ∀ x ∈ cellE w, x ∉ cellE (cellJ c s j))
    (hm1 : ¬ IsMid c s k (back1 w tw)) (hm2 : ¬ IsMid c s k (back2 w tw))
    (hsplit : ¬ Conn (flip F w) (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    ¬ NoTypeIII V (flipCol F c s (k + 2)) := by sorry
