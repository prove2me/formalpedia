-- Prove2me | Theorems.Thm_VWZClique_IntegerRAM_Projected_SquareCaller_square_run
-- name    : VWZClique.IntegerRAM.Projected.SquareCaller.square_run
-- status  : Proved
-- author  : @orz
-- created : 2026-11-20T14:03:32.953184+00:00
-- url     : https://prove2.me/theorems/027a8a4a-622b-4975-be00-16c54c42c9c0
-- title:
--   Native square multiplication on a projected matrix tile
-- statement:
--   A fixed integer bilinear scheme can be called once on each pair of packed square tiles. Given sufficient word width and disjoint input, output and scratch arrays, the program returns their matrix product multiplied by the scheme scale to the recursion depth. It preserves the caller’s input tiles, saved registers, and live memory prefix. The cost bound includes copying and padding ordinary row-major matrices.
-- source:
--   Virginia Vassilevska Williams and Or Zamir, The k-Clique hypothesis is dead, for good. https://zamir.prof/kclq.pdf, Section 3 (doubly projected contraction) and Appendix A (implementing matrix products in the word RAM).

import Definitions.Def_VWZClique_NativeCliqueCompiler
open VWZClique VWZClique.IntegerRAM VWZClique.BlockMM VWZClique.BlockMM.WordLayout VWZClique.IntegerRAM.Structured VWZClique.IntegerRAM.Projected VWZClique.IntegerRAM.SquareCode VWZClique.IntegerRAM.SquareCode.Layout VWZClique.IntegerRAM.Projected.SquareCaller

/-- Discharge the concrete square-call interface for the projected contraction. -/
theorem VWZClique.IntegerRAM.Projected.SquareCaller.square_run {b r W M s t : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hr : 0<r)
    (hs : 1 ≤ s) (room : VWZClique.IntegerRAM.SquareCode.Layout.Room W M) (l : Projected.Layout) (A : Tile s) (B C : Fin t → Tile s)
    (leftB : l.lhs+t*(s*s) ≤ l.prod) (rightB : l.rhs+t*(s*s) ≤ l.prod)
    (weightB : l.wt+s*s ≤ l.prod) (keep : l.preserve ≤ l.prod)
    (workspace : l.prod+s*s+space b r (depth b s) 1 ≤ M) :
    SquareRun W (duration S s) (S.scale^(depth b s)) (multiply S) l A B C := by sorry
