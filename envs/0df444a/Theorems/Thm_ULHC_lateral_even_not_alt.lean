-- Prove2me | Theorems.Thm_ULHC_lateral_even_not_alt
-- name    : ULHC.lateral_even_not_alt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:44:40.602174+00:00
-- url     : https://prove2.me/theorems/9a16656c-39a0-4f26-83dc-bfbd06507234
-- title:
--   ULHC: lateral even not alt
-- statement:
--   The ULHC construction uses the lateral even not alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L344-L388
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L344-L388

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hk hcell hpat

theorem ULHC.lateral_even_not_alt {j : ℕ} (hj : j ≤ k) (hje : j % 2 = 0) :
    ¬ Alt (flipCol F c s (k + 2)) (nb (cellJ c s j) (latA s)) ∧
      ¬ Alt (flipCol F c s (k + 2)) (nb (cellJ c s j) (latB s)) := by sorry
