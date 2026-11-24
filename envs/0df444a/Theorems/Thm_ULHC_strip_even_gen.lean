-- Prove2me | Theorems.Thm_ULHC_strip_even_gen
-- name    : ULHC.strip_even_gen
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:50:18.845347+00:00
-- url     : https://prove2.me/theorems/3899d3d7-c0e9-4b9e-8879-0e79eb85861e
-- title:
--   ULHC: strip even gen
-- statement:
--   The ULHC construction uses the strip even gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Counts.lean#L107-L140
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Counts.lean#L107-L140

import Definitions.Def_ULHC_Reroute
import Definitions.Def_ULHC_Counts
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {c : Pt} {s : Side}

theorem ULHC.strip_even_gen (k : ℕ) (hk : k % 2 = 0) (F : Finset Edge) (hF : Deg2 V F)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) :
    ncomp V (flipCol F c s (k + 2)) = ncomp V F ∨
      ncomp V (flipCol F c s (k + 2)) + 2 = ncomp V F := by sorry
