-- Prove2me | Theorems.Thm_ULHC_end_flip_sep
-- name    : ULHC.end_flip_sep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:37:41.755998+00:00
-- url     : https://prove2.me/theorems/456e26f3-fa72-4da7-9ee1-a6cec4f34565
-- title:
--   ULHC: end flip sep
-- statement:
--   The ULHC construction uses the end flip sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L117-L120
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L117-L120

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hT hk hcell hpat hsep

theorem ULHC.end_flip_sep : ¬ Conn (flip F (cellJ c s (k + 1))) (back1 (cellJ c s (k + 1)) s)
    (front1 (cellJ c s (k + 1)) s) := by sorry
