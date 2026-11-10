-- Prove2me | Theorems.Thm_Width4HSG_Main_lemma_10_2
-- name    : Width4HSG.Main.lemma_10_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:19:13.12862+00:00
-- url     : https://prove2.me/theorems/4e3e98ed-bcd5-4a0d-8783-9cd13bc209c3
-- title:
--   Lemma 10.2 — HSG error reduction
-- statement:
--   Lemma 10.2 (HSG error reduction [DH25, Lemma 4.7]). Suppose H hits every length-n, width-four ROBP of density greater than 1/4. For every 0 < ε ≤ 1, the set H^{⊛t}, with t = ⌈2 ln(2/ε)⌉, (10.4) hits every such program of density at least ε.
--
--
--
--   Differences from the source:
--   - encoding: uniform distributions and expectations on Boolean words → finite Boolean functions, PMF laws and normalized finite sums; reason: these are the same finite sample spaces and probability laws
--   - encoding: width at most w, reads x1 through xn → Fin w padded states and zero-based ordered transitions; reason: unreachable padding and index translation preserve every accepted function
--   - encoding: position-aligned t-fold splice with t = ceil(2 ln(2/ε)) → alignedSplice with a natural ceiling of the natural-log expression; reason: the expression is positive on 0 < ε ≤ 1; nondecreasing cuts allow empty blocks
-- source:
--   Krak, Beyond Width-3: Better Hitting Set Generators for Width-4 Read-Once Branching Programs, STOC 2027 submission, Lemma 10.2, p. 85, PDF SHA256 4ef018bd96382f87d7be4ed375c984df83c46ccdc42ab98e0d7d589b27b1c050

import Mathlib
import Definitions.Def_Width4HSG_Main_Splice

noncomputable section
open scoped BigOperators

namespace Width4HSG.Main

theorem lemma_10_2 {n : ℕ} (hn : 4 ≤ n) (H : Set (Bits n))
    (hH : ∀ P : ROBP 4 n, (1/4 : ℝ) < density P.eval → Hits H P.eval)
    (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∀ P : ROBP 4 n, ε ≤ density P.eval →
      Hits (alignedSplice H ⌈2 * Real.log (2/ε)⌉₊) P.eval
 := by sorry

end Width4HSG.Main
