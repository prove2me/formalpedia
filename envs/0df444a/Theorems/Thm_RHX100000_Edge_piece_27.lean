-- Prove2me | Theorems.Thm_RHX100000_Edge_piece_27
-- name    : RHX100000.Edge.piece_27
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:43:32.120517+00:00
-- url     : https://prove2.me/theorems/1e476465-a5c1-4385-b0f1-2d9598c8823e
-- title:
--   Edge piece 27 at height 100000 passes the piece checker
-- statement:
--   Octant piece 27 of the edge data `RHX_Edge100000Data` passes the framework's piece checker:
--
--   $$
--   \texttt{H11K.pieceJ}\ E\ 27=\texttt{true},
--   $$
--
--   that is, the Euler–Maclaurin evaluation of $\zeta$ at the piece centre with $N=30000$ terms, the octant check of the Taylor model on the piece disc, the remainder and budget side conditions, and both breakpoints inside the piece radius. By the published `H11K.edge_sound_of_split`, these per-piece facts and `RHX100000.Edge.rest` give the horizontal argument-change enclosure at height $100000$.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000) to height 100000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
import Definitions.Def_RHX_Edge100000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4

theorem RHX100000.Edge.piece_27 : H11K.pieceJ RHX100000.Edge.E 27 = true := by
  sorry
