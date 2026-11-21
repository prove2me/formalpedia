-- Prove2me | Theorems.Thm_VWZClique_IntegerRAM_Projected_Preparation_run
-- name    : VWZClique.IntegerRAM.Projected.Preparation.run
-- status  : Proved
-- author  : @orz
-- created : 2026-11-20T14:07:01.25404+00:00
-- url     : https://prove2.me/theorems/fc5f1bd6-223a-4758-8cee-f913abc112ab
-- title:
--   Preparing the interpolation and projection tables on the word RAM
-- statement:
--   At a recursion frame of depth at most $36$, a fixed sequence of word-RAM instructions prepares the projected contraction for a weighted nine-vertex graph pattern. For $n=2^L$, it computes the retained mask and label records, the arrays of signs and partner indices for the $L$-coordinate basis, and the scale used by the size-$n$ matrix multiplications. It also preserves the input weight table and the protected words of the recursion frame. The theorem gives the instruction count and explicit word-size and address bounds for this initialization.
-- source:
--   V. Vassilevska Williams and O. Zamir, “The k-Clique hypothesis is dead, for good,” Theorem 1.1 and Appendix A. https://zamir.prof/kclq.pdf

import Mathlib
import Definitions.Def_VWZClique_NativeCliqueCompiler
open VWZClique VWZClique.IntegerRAM VWZClique.IntegerRAM.Projected VWZClique.IntegerRAM.Projected.Preparation VWZClique.IntegerRAM.Structured VWZClique.UniformFolds VWZClique.IntegerRAM.NativeFrame VWZClique.NativeTraversal VWZClique.IntegerRAM.NativeArena VWZClique.BlockMM

theorem VWZClique.IntegerRAM.Projected.Preparation.run {W M L root output d b c : ℕ} (large : 512≤ root) (hd : d≤36) (hb : 2≤ b)
    (H : SimpleGraph V) (w : WeightKey (2^L)→ℚ) (q : List (NativeTraversal.Slot L)) (m : Memory)
    (room : Graph.Division.Room W M)
    (supportRoom : MaskScan.Arena.slot (atDepth root (2^L) d) (2^L) 7+2+3*8^L≤ M)
    (ratio : 2^(L+1)*(4*windowAt (Nat.card H.edgeSet))≤ M) (padding : b*2^L+1≤ M)
    (src : Repr (layout L root output large) (.input d w::q) m) :
    let base := atDepth root (2^L) d
    let K := windowAt (Nat.card H.edgeSet)
    let count := (RankSwap.outside L (lower K L) (width K L)).card
    ∃ f≤ ticks d K b c L, ∃ o, Runs W (command d K b c) m f o ∧ Ready L K base count b c w o ∧
      ∀ z : ℕ, projectionPrefix base (2^L) z → o z=m z := by sorry
