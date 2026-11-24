-- Prove2me | Theorems.Thm_ULHC_besideA_not_mem
-- name    : ULHC.besideA_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:19:44.278512+00:00
-- url     : https://prove2.me/theorems/ea6c39d1-0d05-455d-89ce-8fdb41017419
-- title:
--   ULHC: beside A not mem
-- statement:
--   The ULHC construction uses the beside A not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L600-L604
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L600-L604

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.besideA_not_mem (c : Pt) (s : Side) {m j i : ℕ} (hi : i < m) {x : Edge}
    (hx : x ∈ cellE (cellJ (nb (cellJ c s m) (latA s)) s j)) : x ∉ cellE (cellJ c s i) := by sorry
