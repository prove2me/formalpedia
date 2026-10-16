-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_bracket_tree_sound
-- name    : TaoFivePrimes.rh_batch01_height_bracket_tree_sound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T17:01:34.339029+00:00
-- url     : https://prove2.me/theorems/51a6c213-1003-434f-af3b-b9377cffc004
-- title:
--   TaoFivePrimes.rh_batch01_height_bracket_tree_sound
-- statement:
--   The list interpretation of an indexed proof-carrying bracket tree has its advertised number of leaves, ordered disjoint coordinate brackets, and bounds inside the tree span. This is a general structural soundness theorem. It does not prove any normalized zeta enclosure.
-- source:
--   Finite structural sign and order certificates, generated from the native FLINT 3.6.0 Platt FFT/interpolation proposal on [3289999744,3289999872]. Numeric tests are necessary constructor proof fields and use ordinary decide +kernel. No value containment, total zero count or RH conclusion is asserted. Platt method: DOI 10.1090/mcom/3198. The surrounding project preserves attribution to sometik179 (c9908072-d99a-4431-aad8-a72c6352619a) and Gabewhigham. The interpretation uses the Mathlib completed-zeta normalization from the separately accepted normalization theorem.

import Definitions.Def_TaoFivePrimes_RHBatch01HeightBracketInterface

theorem TaoFivePrimes.rh_batch01_height_bracket_tree_sound {l r n : Nat} (t : RHBatch01HeightBracketData.Tree l r n) :
    (RHBatch01HeightBracketInterface.leaves t).length=n ∧
    (RHBatch01HeightBracketInterface.leaves t).Pairwise (fun p q => p.r≤q.l) ∧
    (∀ p ∈ RHBatch01HeightBracketInterface.leaves t, l≤p.l ∧ p.r≤r) := by sorry
