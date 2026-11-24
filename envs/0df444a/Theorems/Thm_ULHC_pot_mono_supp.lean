-- Prove2me | Theorems.Thm_ULHC_pot_mono_supp
-- name    : ULHC.pot_mono_supp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:42.724637+00:00
-- url     : https://prove2.me/theorems/53131b29-9ad9-4399-be20-2697d8480204
-- title:
--   ULHC: pot mono supp
-- statement:
--   The ULHC construction uses the pot mono supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean#L143-L148
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean#L143-L148

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential
set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ}

theorem ULHC.pot_mono_supp {E E' : Finset Edge} (hsub : E ⊆ E') (hS : Supp E w) (c : Pt) :
    pot E w c = pot E' w c := by sorry
