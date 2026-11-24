-- Prove2me | Theorems.Thm_ULHC_body_not_alt
-- name    : ULHC.body_not_alt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:56:46.50615+00:00
-- url     : https://prove2.me/theorems/3d49766d-2928-4862-be29-9f5df4ccba23
-- title:
--   ULHC: body not alt
-- statement:
--   The ULHC construction uses the body not alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L304-L309
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L304-L309

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
omit hs x0 hconn hF hT hcell hsep hT' hz

theorem ULHC.body_not_alt {j : ℕ} (hj : j ≤ k) {tw : Side} (l1 : lat1 (cellJ c s j) tw ∈ F)
    (l2 : lat2 (cellJ c s j) tw ∈ F) (bw : back (cellJ c s j) tw ∉ F)
    (fw : front (cellJ c s j) tw ∉ F) : False := by sorry
