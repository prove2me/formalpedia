-- Prove2me | Theorems.Thm_ULHC_creach_succ
-- name    : ULHC.creach_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:36:25.499455+00:00
-- url     : https://prove2.me/theorems/ee7bb2b3-dc0a-41cc-b718-3d12b9077d04
-- title:
--   ULHC: creach succ
-- statement:
--   The ULHC construction uses the creach succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Comp.lean#L47-L48
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Comp.lean#L47-L48

import Definitions.Def_ULHC_TwoFactor
import Definitions.Def_ULHC_Comp
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge}

theorem ULHC.creach_succ (x : Pt) (k : ℕ) :
    creach F x (k + 1) = creach F x k ∪ (creach F x k).biUnion (fnbr F) := by sorry
