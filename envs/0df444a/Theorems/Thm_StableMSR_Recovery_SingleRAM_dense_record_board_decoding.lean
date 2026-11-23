-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleRAM_dense_record_board_decoding
-- name    : StableMSR.Recovery.SingleRAM.dense_record_board_decoding
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-23T00:09:15.63959+00:00
-- url     : https://prove2.me/theorems/8a4579b0-3bd5-406c-8a9d-b598ae076e85
-- title:
--   The packed record array decodes to the exact circuit, roots and every point bit
-- statement:
--   Exact arithmetic decoding identifies the record type, destination, predecessor, root and every point-membership bit. The proof includes both parity cases of the flat two-cell output and all unused instruction slots.
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

theorem StableMSR.Recovery.SingleRAM.dense_record_board_decoding (x : World) (k H : ℕ) (m : ℕ→ℤ) (g : Gates) (roots : ℕ→ℕ)
    (hk : 0< x.k) (hn : 0< x.n) (eqk : k=x.k) (eqH : H=x.rows)
    (big : 1+5*(1+3*g.size*x.n*x.n)< H) (src : Input x g roots)
    (head : (m 0).toNat=3*g.size) (wr : Writes x {x with k:=k,rows:=H,mem:=m} packCell) :
    denotes {x with k:=k,rows:=H,mem:=m} g roots := by sorry
