-- Prove2me | Theorems.Thm_ULHC_start_allConn
-- name    : ULHC.start_allConn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:50:33.100409+00:00
-- url     : https://prove2.me/theorems/cf80c15b-cf02-49ec-855e-c8a9f70c7cd4
-- title:
--   ULHC: start all Conn
-- statement:
--   The ULHC construction uses the start all Conn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Created.lean#L71-L86
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Created.lean#L71-L86

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
omit hs x0 hconn hF hT

theorem ULHC.start_allConn : AllConn (flipCol F c s (k + 2)) c := by sorry
