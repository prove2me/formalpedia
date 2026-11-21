-- Prove2me | Theorems.Thm_VWZClique_IntegerRAM_Projected_Large_from_dense
-- name    : VWZClique.IntegerRAM.Projected.Large.from_dense
-- status  : Proved
-- author  : @orz
-- created : 2026-11-20T14:03:26.21535+00:00
-- url     : https://prove2.me/theorems/5588f5dc-2eee-4b3b-8afb-91c96bf49537
-- title:
--   Exact word-RAM trace contraction from three dense projected tables
-- statement:
--   Given three correctly packed dense projected channels with a common integer factor, a fixed word-RAM program computes their trace contraction. Its accumulator holds the projected numerator multiplied by the cube of the incoming factor and by the scale of one large square product. The program also records that product scale, preserves the memory preceding the temporary array, and runs within the explicit tile cost.
-- source:
--   Virginia Vassilevska Williams and Or Zamir, The k-Clique hypothesis is dead, for good. https://zamir.prof/kclq.pdf, Section 3 (doubly projected contraction) and Appendix A (implementing matrix products in the word RAM).

import Definitions.Def_VWZClique_NativeCliqueCompiler
open VWZClique VWZClique.IntegerRAM VWZClique.BlockMM VWZClique.BlockMM.WordLayout VWZClique.IntegerRAM.Structured VWZClique.IntegerRAM.Projected VWZClique.IntegerRAM.SquareCode VWZClique.IntegerRAM.SquareCode.Layout VWZClique.UniformFolds VWZClique.TraceDyadic VWZClique.Double VWZClique.Double.IntegerTiling VWZClique.IntegerRAM.Projected.Large

/-- From the dense scaled channels, compute the projected trace in the native
accumulator. The only private positive word before the packed tiles is the
now-dead transform word at l.temp. Every earlier address is preserved. -/
theorem VWZClique.IntegerRAM.Projected.Large.from_dense {base rank q W M L : ℕ} (S : Scheme base rank) (hb : 2 ≤ base) (hr : 0<rank)
    (labels : Finset (BasisLabel L)) (w : ChannelKey L → ℚ) (small : ℤ) (K : ℕ)
    (l : Banks) (m : IntegerRAM.Memory) (ptr : Pointers m l)
    (room : VWZClique.IntegerRAM.Graph.Division.Room W M) (N : m 0=((2^L:ℕ):ℤ)) (len : m 320=L) (card : m 359=labels.card) :
    let shape := effectiveTile q L labels.card
    let s := IntegerTiling.side L shape
    let n := blocks L shape
    let A := scaleMat small (shortWeight labels K w)
    let B := scaleMat small (middle labels shape w)
    let C := scaleMat small (Projected.right labels shape w)
    Limits base rank q L labels.card s n l M → Sources m l A B C →
      ∃ f≤cost q S L s n, ∃ o, Runs W (VWZClique.IntegerRAM.Projected.Large.code q S) m f o ∧
        o VWZClique.IntegerRAM.Projected.Cell.acc=(small^3*S.scale^(depth base s))*numerator labels labels K K w ∧
        o VWZClique.IntegerRAM.SquareCode.Layout.scaleReg=S.scale^(depth base s) ∧ ∀ z : ℕ, z<l.temp → o z=m z := by sorry
