-- Prove2me | Theorems.Thm_ULHC_side_chain1
-- name    : ULHC.side_chain1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:34:26.793905+00:00
-- url     : https://prove2.me/theorems/83b72f02-73fb-47b5-8d6a-5f666b02ceb3
-- title:
--   ULHC: side chain1
-- statement:
--   The ULHC construction uses the side chain1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearChain.lean#L55-L68
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearChain.lean#L55-L68

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i0 : ℕ} (hz : SigFrom F z tf m i0)
include hF hT hk hcell hpat hsep hz

theorem ULHC.side_chain1 : ∀ j i, j ≤ k → i0 ≤ i → i < m → cellJ z tf i = nb (cellJ c s j) (latA s) →
    tf = s.opp ∧ ∃ ie, i ≤ ie ∧ ie < m ∧ ie % 2 = 0 ∧ cellJ z tf ie = nb c (latA s) := by sorry
