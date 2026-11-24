-- Prove2me | Theorems.Thm_ULHC_stripLen_eq_some
-- name    : ULHC.stripLen_eq_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:51:21.706816+00:00
-- url     : https://prove2.me/theorems/f7254a81-934b-4e55-84ca-006a8ecc67d2
-- title:
--   ULHC: strip Len eq some
-- statement:
--   The ULHC construction uses the strip Len eq some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Enum.lean#L104-L118
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Enum.lean#L104-L118

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
set_option autoImplicit true
open ULHC
open Finset
variable (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side)
variable {V F c s}

theorem ULHC.stripLen_eq_some {n : ℕ} :
    stripLen V F c s = some n ↔
      1 ≤ n ∧ StripPat F c s n ∧ ∀ j < n, IsCell V (cellJ c s j) := by sorry
