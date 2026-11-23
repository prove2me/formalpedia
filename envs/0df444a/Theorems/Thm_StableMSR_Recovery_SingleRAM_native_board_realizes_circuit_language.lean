-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleRAM_native_board_realizes_circuit_language
-- name    : StableMSR.Recovery.SingleRAM.native_board_realizes_circuit_language
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T00:14:50.129555+00:00
-- url     : https://prove2.me/theorems/f4780a2f-dd12-4d6f-89a8-2896e798be03
-- title:
--   A packed circuit has exactly its ordered gate language on every physical state
-- statement:
--   Transport the physical tag, destination, predecessor and mask fields through each trace constructor. The three-record circuit theorem then identifies every ordered witness, including unreachable states and empty outputs.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution specializes the mission’s tight-block recurrence to singleton progress for the native separator construction.

import Definitions.Def_StableMSR_DenseSingletonCompilation
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 15000
open StableMSR.Recovery StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleCircuit
open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog
open StableMSR.Recovery.WindowProfiles (subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Writes field)
open StableMSR.Recovery.SingleRAM
open StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleWindows
open StableMSR.Recovery.WindowProfiles (piece keys)

theorem StableMSR.Recovery.SingleRAM.native_board_realizes_circuit_language (y : World) (g : Gates) (roots : ℕ→ℕ) (repr : denotes y g roots) (nonempty : 0< g.size) (zero : gateAt g 0=.atom [])
    (p : ℕ) (L : List (Cluster y.n)) : WindowMasks.Trace (board y) (block y) p L ↔ Language y.n g p L := by sorry
