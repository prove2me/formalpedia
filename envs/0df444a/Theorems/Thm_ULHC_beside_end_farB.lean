-- Prove2me | Theorems.Thm_ULHC_beside_end_farB
-- name    : ULHC.beside_end_farB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:38:23.082401+00:00
-- url     : https://prove2.me/theorems/80f6aaea-a222-4d51-8f83-8da28141c2b1
-- title:
--   ULHC: beside end far B
-- statement:
--   The ULHC construction uses the beside end far B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L853-L858
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L853-L858

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.beside_end_farB (c : Pt) (s : Side) (k : ℕ) {n : ℕ} (hn : 2 ≤ n) {x : Edge}
    (hx : x ∈ cellE (cellJ (nb (cellJ c s (k + 1)) (latB s)) s (n - 1))) :
    ∀ j < k + 2, x ∉ cellE (cellJ c s j) := by sorry
