-- Prove2me | Theorems.Thm_ULHC_nOn_front_last
-- name    : ULHC.nOn_front_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:41:23.010529+00:00
-- url     : https://prove2.me/theorems/60a1e568-d744-4ab6-a83e-faa11978db44
-- title:
--   ULHC: n On front last
-- statement:
--   The ULHC construction uses the n On front last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L767-L776
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L767-L776

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.nOn_front_last (m : ℕ) : nOn c s (m + 1) (front (cellJ c s m) s) = 1 := by sorry
