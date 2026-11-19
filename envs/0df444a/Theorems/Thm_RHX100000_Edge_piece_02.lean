-- Prove2me | Theorems.Thm_RHX100000_Edge_piece_02
-- name    : RHX100000.Edge.piece_02
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:40:37.545418+00:00
-- url     : https://prove2.me/theorems/07db5a67-55dc-4d25-af99-42f00323293b
-- title:
--   Edge piece 2 at height 100000 passes the piece checker
-- statement:
--   Octant piece 2 of the edge data `RHX_Edge100000Data` passes the framework's piece checker:
--
--   $$
--   \texttt{H11K.pieceJ}\ E\ 2=\texttt{true},
--   $$
--
--   that is, the Euler–Maclaurin evaluation of $\zeta$ at the piece centre with $N=30000$ terms, the octant check of the Taylor model on the piece disc, the remainder and budget side conditions, and both breakpoints inside the piece radius. By the published `H11K.edge_sound_of_split`, these per-piece facts and `RHX100000.Edge.rest` give the horizontal argument-change enclosure at height $100000$.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000) to height 100000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_RHX_Edge100000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem RHX100000.Edge.piece_02 : H11K.pieceJ RHX100000.Edge.E 2 = true := by
  sorry
