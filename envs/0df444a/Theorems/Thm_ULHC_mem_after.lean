-- Prove2me | Theorems.Thm_ULHC_mem_after
-- name    : ULHC.mem_after
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:26:58.410816+00:00
-- url     : https://prove2.me/theorems/a1b07b8d-42bf-456c-9988-9b219d059697
-- title:
--   ULHC: mem after
-- statement:
--   The ULHC construction uses the mem after property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L140-L141
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L140-L141

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hk : k % 2 = 0) (hpat : StripPat F c s (k + 2))
include hk hpat
omit hk hpat

theorem ULHC.mem_after (e : Edge) :
    e ∈ flipCol F c s (k + 2) ↔ (e ∈ F ↔ nOn c s (k + 2) e % 2 = 0) := by sorry
