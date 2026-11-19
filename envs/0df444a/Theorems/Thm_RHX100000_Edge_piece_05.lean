-- Prove2me | Theorems.Thm_RHX100000_Edge_piece_05
-- name    : RHX100000.Edge.piece_05
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:40:30.491259+00:00
-- url     : https://prove2.me/theorems/242f7d23-7cc2-4303-ab0a-f869451617a9
-- title:
--   Edge piece 5 at height 100000 passes the piece checker
-- statement:
--   Octant piece 5 of the edge data `RHX_Edge100000Data` passes the framework's piece checker:
--
--   $$
--   \texttt{H11K.pieceJ}\ E\ 5=\texttt{true},
--   $$
--
--   that is, the Euler–Maclaurin evaluation of $\zeta$ at the piece centre with $N=30000$ terms, the octant check of the Taylor model on the piece disc, the remainder and budget side conditions, and both breakpoints inside the piece radius. By the published `H11K.edge_sound_of_split`, these per-piece facts and `RHX100000.Edge.rest` give the horizontal argument-change enclosure at height $100000$.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000) to height 100000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_RHX_Edge100000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem RHX100000.Edge.piece_05 : H11K.pieceJ RHX100000.Edge.E 5 = true := by
  sorry
