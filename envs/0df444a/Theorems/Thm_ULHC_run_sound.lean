-- Prove2me | Theorems.Thm_ULHC_run_sound
-- name    : ULHC.run_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:59:57.785493+00:00
-- url     : https://prove2.me/theorems/c2cf8386-1ef1-4761-9ad0-723e80d946cd
-- title:
--   ULHC: run sound
-- statement:
--   The ULHC construction uses the run sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Algorithm.lean#L114-L131
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Algorithm.lean#L114-L131

import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_Algorithm
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.run_sound {V : Finset Pt} : ∀ (k : ℕ) (G : Finset Edge), Deg2 V G → run V k G = true →
    ∃ H, Deg2 V H ∧ ncomp V H = 1 := by sorry
