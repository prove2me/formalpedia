-- Prove2me | Theorems.Thm_ULHC_besideB_not_mem
-- name    : ULHC.besideB_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:19:55.147354+00:00
-- url     : https://prove2.me/theorems/db33604b-1902-4b80-8652-8485a3364055
-- title:
--   ULHC: beside B not mem
-- statement:
--   The ULHC construction uses the beside B not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L606-L610
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L606-L610

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.besideB_not_mem (c : Pt) (s : Side) {m j i : ℕ} (hi : i < m) {x : Edge}
    (hx : x ∈ cellE (cellJ (nb (cellJ c s m) (latB s)) s j)) : x ∉ cellE (cellJ c s i) := by sorry
