-- Prove2me | Theorems.Thm_ULHC_poly8
-- name    : ULHC.poly8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:12:27.147028+00:00
-- url     : https://prove2.me/theorems/c90cfc15-ca28-4553-b563-1c36f32e2941
-- title:
--   ULHC: poly8
-- statement:
--   The ULHC construction uses the poly8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostAlg.lean#L131-L147
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostAlg.lean#L131-L147

import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_CostTwoFactor
import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostAlg
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}

theorem ULHC.poly8 (N n : ℕ) (hN : 1 ≤ N) (hn : n ≤ 24 * N ^ 2) :
    n ^ 2 + n * (n * (n * (300 * N ^ 2 + n + 5) + 4)) + n * (160 * N ^ 2 + n + 3) + n + 4 ≤
      5000000 * N ^ 8 := by sorry
