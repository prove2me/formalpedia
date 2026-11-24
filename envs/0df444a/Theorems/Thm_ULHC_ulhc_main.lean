-- Prove2me | Theorems.Thm_ULHC_ulhc_main
-- name    : ULHC.ulhc_main
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:38:11.256858+00:00
-- url     : https://prove2.me/theorems/869dd1a2-6855-445a-b8a0-8735399c7fbd
-- title:
--   ULHC: ulhc main
-- statement:
--   The ULHC construction uses the ulhc main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Main.lean#L19-L24
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Main.lean#L19-L24

import Definitions.Def_ULHC_PathComplete
import Definitions.Def_ULHC_Timed_Alg
import Definitions.Def_ULHC_Main
set_option autoImplicit true
open ULHC

theorem ULHC.ulhc_main {V : Finset Pt} (hs : Solid V) :
    ((T.ulhcT V).ret = true ↔ ∃ H, Deg2 V H ∧ ncomp V H = 1) ∧
      (T.ulhcT V).time ≤ 500000000 * (V.card + 1) ^ 12 := by sorry
