-- Prove2me | Theorems.Thm_ULHC_ulhc_correct
-- name    : ULHC.ulhc_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:08:26.749881+00:00
-- url     : https://prove2.me/theorems/b995a877-0c3e-41ab-84cf-0d85ed8465ab
-- title:
--   ULHC: ulhc correct
-- statement:
--   **Umans–Lenhart.** For a solid grid graph `V`, the algorithm `ulhc` answers `true` exactly
--   when `V` has a Hamiltonian cycle (a 2-factor with one component).
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L631-L636
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L631-L636

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.ulhc_correct {V : Finset Pt} (hs : Solid V) :
    ulhc V = true ↔ ∃ H, Deg2 V H ∧ ncomp V H = 1 := by sorry
