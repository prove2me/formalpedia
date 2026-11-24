-- Prove2me | Theorems.Thm_RHX1000000_Edge_piece_32
-- name    : RHX1000000.Edge.piece_32
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T03:50:15.99618+00:00
-- url     : https://prove2.me/theorems/d38635fe-8645-4926-9d56-3c3af4bf7882
-- title:
--   Edge piece 32 at height 1000000 passes the piece checker
-- statement:
--   Octant piece 32 of the edge data `RHX_Edge1000000Data` passes the framework's piece checker:
--
--   $$
--   \texttt{H11K.pieceJ}\ E\ 32=\texttt{true},
--   $$
--
--   that is, the Euler–Maclaurin evaluation of $\zeta$ at the piece centre with $N=300000$ terms, the octant check of the Taylor model on the piece disc, the remainder and budget side conditions, and both breakpoints inside the piece radius.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
import Definitions.Def_ArdaRS_Config64
import Definitions.Def_RHX1E6_RunE32
import Definitions.Def_RHX_Edge1000000Data
import Definitions.Def_RHX_RunChain
import Definitions.Def_RHX_RunSplit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open ArbEcon.Off

theorem RHX1000000.Edge.piece_32 : H11K.pieceJ RHX1000000.Edge.E 32 = true := by
  sorry
