-- Prove2me | Theorems.Thm_ULHC_nb_cellJ
-- name    : ULHC.nb_cellJ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:46:30.205493+00:00
-- url     : https://prove2.me/theorems/9ebd99a5-8c18-4f48-aa6d-934ff4ec8873
-- title:
--   ULHC: nb cell J
-- statement:
--   The ULHC construction uses the nb cell J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Strip.lean#L90-L92
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Strip.lean#L90-L92

import Definitions.Def_ULHC_Iso
import Definitions.Def_ULHC_Strip
set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)

theorem ULHC.nb_cellJ (j : ℕ) : nb (cellJ c s j) s = cellJ c s (j + 1) := by sorry
