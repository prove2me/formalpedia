-- Prove2me | Theorems.Thm_RHX1000000_Edge_piece_08
-- name    : RHX1000000.Edge.piece_08
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T01:36:52.686077+00:00
-- url     : https://prove2.me/theorems/1d06c8cf-627c-4d26-bf3c-2c7d69a4e1d1
-- title:
--   Edge piece 8 at height 1000000 passes the piece checker
-- statement:
--   Octant piece 8 of the edge data `RHX_Edge1000000Data` passes the framework's piece checker:
--
--   $$
--   \texttt{H11K.pieceJ}\ E\ 8=\texttt{true},
--   $$
--
--   that is, the Euler–Maclaurin evaluation of $\zeta$ at the piece centre with $N=300000$ terms, the octant check of the Taylor model on the piece disc, the remainder and budget side conditions, and both breakpoints inside the piece radius.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
import Definitions.Def_ArdaRS_Config64
import Definitions.Def_RHX1E6_RunE08
import Definitions.Def_RHX_Edge1000000Data
import Definitions.Def_RHX_RunChain
import Definitions.Def_RHX_RunSplit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open ArbEcon.Off

theorem RHX1000000.Edge.piece_08 : H11K.pieceJ RHX1000000.Edge.E 8 = true := by
  sorry
