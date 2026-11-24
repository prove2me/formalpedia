-- Prove2me | Theorems.Thm_WilliamsonShmoys_RAMReachesWithin_step
-- name    : WilliamsonShmoys.RAMReachesWithin.step
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T06:02:56.2539+00:00
-- url     : https://prove2.me/theorems/c1ef21e5-5bf6-4f02-ade1-edea9231b669
-- title:
--   One operation reaches the next state
-- statement:
--   For every program $p$ and state $s$, running $p$ from $s$ reaches the state $\mathrm{step}_p(s)$ within one operation.
--
--   This is the base case for building specifications of single instructions.
--
--   **Formalization Note.** $\mathrm{run}_p(s,t)$ is `planarRAMRun p s t`, the $t$-fold iterate of `planarRAMStep p`; triples are `RAMSpec` from `Def_WilliamsonShmoys_RAMSpec`.
-- source:
--   Program-logic infrastructure for the RAM model of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMSpec

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.RAMReachesWithin.step (program : List PlanarRAMInstruction) (s : PlanarRAMState) :
    RAMReachesWithin program s (fun s' => s' = planarRAMStep program s) 1 := by sorry
