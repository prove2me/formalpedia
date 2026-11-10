-- Prove2me | Theorems.Thm_Width4HSG_Main_lemma_4_3
-- name    : Width4HSG.Main.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:20:18.901101+00:00
-- url     : https://prove2.me/theorems/0611128e-16e9-4d67-a2df-b708a792739d
-- title:
--   Lemma 4.3 — reduction from width four
-- statement:
--   Lemma 4.3 (reduction from width four [DH25, Lemma 4.5]). Let η∨, η∧ > 0. Suppose H∨, H∧ ⊆ {0, 1}^n satisfy: 1. H∨ hits every length-n, width-three ∨-program of density greater than η∨. 2. H∧ hits every length-n, width-three ∧-program of density greater than η∧. Then H4 = {0^a ◦ x_{a+1:b} ◦ y_{b+1:n} : 0 ≤ a ≤ b ≤ n, x ∈ H∨, y ∈ H∧} hits every ordinary length-n, width-four ROBP B satisfying µ(B) > η∨ + η∧. Moreover, |H4| ≤ (n + 1)^2 |H∨| |H∧|.
--
--
--
--   Differences from the source:
--   - encoding: uniform distributions and expectations on Boolean words → finite Boolean functions, PMF laws and normalized finite sums; reason: these are the same finite sample spaces and probability laws
--   - encoding: width at most w, reads x1 through xn → Fin w padded states and zero-based ordered transitions; reason: unreachable padding and index translation preserve every accepted function
--   - encoding: subsets of the finite cube and their cardinalities → Finset subsets and a membership-defined splice; reason: every subset of this finite cube has this representation; cut indices preserve positions
-- source:
--   Krak, Beyond Width-3: Better Hitting Set Generators for Width-4 Read-Once Branching Programs, STOC 2027 submission, Lemma 4.3, p. 20, PDF SHA256 4ef018bd96382f87d7be4ed375c984df83c46ccdc42ab98e0d7d589b27b1c050

import Mathlib
import Definitions.Def_Width4HSG_Main_EdgeProgram
import Definitions.Def_Width4HSG_Main_Splice

noncomputable section
open scoped BigOperators

namespace Width4HSG.Main

theorem lemma_4_3 {n : ℕ} (hn : 4 ≤ n) (etaOr etaAnd : ℝ)
    (hOr : 0 < etaOr) (hAnd : 0 < etaAnd) (HOr HAnd : Finset (Bits n))
    (hitsOr : ∀ F : EdgeProgram 3 n, etaOr < density F.orEval → Hits (↑HOr) F.orEval)
    (hitsAnd : ∀ F : EdgeProgram 3 n, etaAnd < density F.andEval → Hits (↑HAnd) F.andEval) :
    (∀ B : ROBP 4 n, etaOr + etaAnd < density B.eval →
      Hits (↑(widthFourSplice HOr HAnd)) B.eval) ∧
    (widthFourSplice HOr HAnd).card ≤ (n+1)^2 * HOr.card * HAnd.card
 := by sorry

end Width4HSG.Main
