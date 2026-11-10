-- Prove2me | Theorems.Thm_Width4HSG_Main_lemma_4_2
-- name    : Width4HSG.Main.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:20:33.651196+00:00
-- url     : https://prove2.me/theorems/75d27113-0371-4f4e-8295-cca7c41705a4
-- title:
--   Lemma 4.2 — hitting disjunction programs
-- statement:
--   Lemma 4.2 (hitting ∨-programs [DH25, Lemma 4.3]). For every length-n, width-three ∨-program F, there is an ordinary length-n, width-three ROBP G such that G(x) ≤ F(x) for every x and µ(G) ≥ µ(F)/n. Consequently, a hitting set for ordinary width-three ROBPs of density at least η/n also hits every width-three ∨-program of density at least η.
--
--   Includes the pointwise dominated ROBP and the consequent hitting-set implication; n ≥ 4 is the standing convention of Sections 3–10.
--
--   Differences from the source:
--   - encoding: uniform distributions and expectations on Boolean words → finite Boolean functions, PMF laws and normalized finite sums; reason: these are the same finite sample spaces and probability laws
--   - encoding: width at most w, reads x1 through xn → Fin w padded states and zero-based ordered transitions; reason: unreachable padding and index translation preserve every accepted function
-- source:
--   Krak, Beyond Width-3: Better Hitting Set Generators for Width-4 Read-Once Branching Programs, STOC 2027 submission, Lemma 4.2, p. 20, PDF SHA256 4ef018bd96382f87d7be4ed375c984df83c46ccdc42ab98e0d7d589b27b1c050

import Mathlib
import Definitions.Def_Width4HSG_Main_EdgeProgram

noncomputable section
open scoped BigOperators

namespace Width4HSG.Main

theorem lemma_4_2 {n : ℕ} (hn : 4 ≤ n) :
    (∀ F : EdgeProgram 3 n, ∃ G : ROBP 3 n,
      (∀ x, indicator (G.eval x) ≤ indicator (F.orEval x)) ∧
      density F.orEval / n ≤ density G.eval) ∧
    (∀ (η : ℝ) (H : Set (Bits n)),
      (∀ G : ROBP 3 n, η / n ≤ density G.eval → Hits H G.eval) →
      ∀ F : EdgeProgram 3 n, η ≤ density F.orEval → Hits H F.orEval)
 := by sorry

end Width4HSG.Main
