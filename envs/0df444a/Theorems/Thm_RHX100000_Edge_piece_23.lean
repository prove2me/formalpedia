-- Prove2me | Theorems.Thm_RHX100000_Edge_piece_23
-- name    : RHX100000.Edge.piece_23
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:43:26.47994+00:00
-- url     : https://prove2.me/theorems/e3a313c1-e064-4c66-bf62-6e890b6f1d7e
-- title:
--   Edge piece 23 at height 100000 passes the piece checker
-- statement:
--   Octant piece 23 of the edge data `RHX_Edge100000Data` passes the framework's piece checker:
--
--   $$
--   \texttt{H11K.pieceJ}\ E\ 23=\texttt{true},
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

theorem RHX100000.Edge.piece_23 : H11K.pieceJ RHX100000.Edge.E 23 = true := by
  sorry
