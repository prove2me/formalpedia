-- Prove2me | Theorems.Thm_ULHC_step_decrease
-- name    : ULHC.step_decrease
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:07:03.949913+00:00
-- url     : https://prove2.me/theorems/9a0e3364-8acf-448e-a50d-048b71110765
-- title:
--   ULHC: step decrease
-- statement:
--   The ULHC construction uses the step decrease property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AlgComplete.lean#L206-L258
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AlgComplete.lean#L206-L258

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
import Theorems.Thm_ULHC_Good_step

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hPC : PathComplete V)
include hs x0 hconn hPC

theorem ULHC.step_decrease {G : Finset Edge} (hG : Deg2 V G) (h2 : 2 ≤ ncomp V G) :
    ∃ G', step V G = some G' ∧ Mz V G' < Mz V G := by sorry
