-- Prove2me | Theorems.Thm_ULHC_run_complete
-- name    : ULHC.run_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:06:47.913534+00:00
-- url     : https://prove2.me/theorems/5d42197a-9739-4c84-a34f-757ca660a725
-- title:
--   ULHC: run complete
-- statement:
--   The ULHC construction uses the run complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AlgComplete.lean#L262-L280
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AlgComplete.lean#L262-L280

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hPC : PathComplete V)
include hs x0 hconn hPC

theorem ULHC.run_complete (hne : V.Nonempty) : ∀ (k : ℕ) (G : Finset Edge), Deg2 V G →
    Mz V G < k → run V k G = true := by sorry
