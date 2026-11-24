-- Prove2me | Theorems.Thm_ULHC_beside_end_farA
-- name    : ULHC.beside_end_farA
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:38:12.533889+00:00
-- url     : https://prove2.me/theorems/23d55b50-8ed5-4675-a892-01ad4712eca8
-- title:
--   ULHC: beside end far A
-- statement:
--   The ULHC construction uses the beside end far A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L846-L851
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L846-L851

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.beside_end_farA (c : Pt) (s : Side) (k : ℕ) {n : ℕ} (hn : 2 ≤ n) {x : Edge}
    (hx : x ∈ cellE (cellJ (nb (cellJ c s (k + 1)) (latA s)) s (n - 1))) :
    ∀ j < k + 2, x ∉ cellE (cellJ c s j) := by sorry
