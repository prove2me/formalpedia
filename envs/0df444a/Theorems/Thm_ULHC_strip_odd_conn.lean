-- Prove2me | Theorems.Thm_ULHC_strip_odd_conn
-- name    : ULHC.strip_odd_conn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:50:03.12194+00:00
-- url     : https://prove2.me/theorems/344c8a1c-6f83-43c5-88dc-6138c0eda2c9
-- title:
--   ULHC: strip odd conn
-- statement:
--   The ULHC construction uses the strip odd conn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Counts.lean#L24-L105
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Counts.lean#L24-L105

import Definitions.Def_ULHC_Reroute
import Definitions.Def_ULHC_Counts
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {c : Pt} {s : Side}

theorem ULHC.strip_odd_conn : ∀ k : ℕ, k % 2 = 0 → ∀ F : Finset Edge, Deg2 V F →
    (∀ j ≤ k, IsCell V (cellJ c s j)) → StripPat F c s (k + 1) →
    Conn F (back1 c s) (front1 c s) → ncomp V (flipCol F c s (k + 1)) = ncomp V F + 1 := by sorry
