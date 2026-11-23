-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleRAM_native_circuit_emitter_with_automatic_allocation
-- name    : StableMSR.Recovery.SingleRAM.native_circuit_emitter_with_automatic_allocation
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T00:17:47.838864+00:00
-- url     : https://prove2.me/theorems/a3e13fe4-6821-4618-87be-701811fe3798
-- title:
--   The native gate emitter allocates its own output arena
-- statement:
--   A fixed command starts from a dense input holding one row allowance per source gate, computes its own polynomial output height, and emits the whole physical board. Its execution bound is a polynomial in the original input capacity, uniformly across all widths and stability factors.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution specializes the mission’s tight-block recurrence to singleton progress for the native separator construction.

import Definitions.Def_StableMSR_SingleCircuitRAM
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 15000
open StableMSR.Recovery StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleCircuit
open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog
open StableMSR.Recovery.WindowProfiles (subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Writes field)
open StableMSR.Recovery.SingleRAM

theorem StableMSR.Recovery.SingleRAM.native_circuit_emitter_with_automatic_allocation : ∃P : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (s : Store) (g : Gates) (roots : ℕ→ℕ),
    0< x.k → 0< x.n → g.size≤ x.rows → Ready x s → Input x g roots →
    ∃t z,Executes x.dist cmd s t z ∧ z≤ P.eval x.cap ∧ let H:=2+5*(1+3*x.rows*x.n*x.n)
      let y:=worldOf x.k H x.dist t;Ready y t ∧ y.mem 1=x.mem 1 ∧ denotes y g roots := by sorry
