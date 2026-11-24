-- Prove2me | Theorems.Thm_ULHC_outer2_body
-- name    : ULHC.outer2_body
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:58:45.645981+00:00
-- url     : https://prove2.me/theorems/b4328d31-fc33-4f8f-8e7c-d8661bfcb5b1
-- title:
--   ULHC: outer2 body
-- statement:
--   The ULHC construction uses the outer2 body property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L209-L225
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L209-L225

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i i0 : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
include hF hpat hcell

theorem ULHC.outer2_body {j : ℕ} (hj : j ≤ k) : outer2 (cellJ c s j) s ∈ F ↔ j % 2 = 0 := by sorry
