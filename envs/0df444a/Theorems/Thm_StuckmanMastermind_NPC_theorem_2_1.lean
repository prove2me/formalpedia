-- Prove2me | Theorems.Thm_StuckmanMastermind_NPC_theorem_2_1
-- name    : StuckmanMastermind.NPC.theorem_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-31T00:53:20.805384+00:00
-- url     : https://prove2.me/theorems/431c77be-0edd-4f59-9cae-c320bdd7be97
-- title:
--   Theorem 2.1 — Mastermind satisfiability is NP-complete
-- statement:
--   The uniform Mastermind satisfiability language is NP-complete, and for every fixed color count κ greater than one the fixed-κ language is NP-complete. Instances contain arbitrary finite lengths and finite sets of explicit guesses with one prescribed black/white feedback pair each. Codes may repeat colors. Both assertions include membership in NP and polynomial-time many-one hardness for every NP language, with complexity measured in the complete encoded input length. No consistency, uniqueness, reduction, or P versus NP assumption is made.
--
--   Differences from the source:
--   - reading: NP-complete with respect to size ℓ (for κ > 1) → uniform NP-completeness and NP-completeness for every fixed κ > 1; reason: retain the stronger fixed-color reading of the ambiguous preamble, with its proof gap recorded as I1.
--   - reading: existential indices shadow the counted indices in Definition 2.1 → counts of matching positions and color multiplicities; reason: the adjacent black/white-peg explanation fixes the intended meaning, recorded as I2.
--   - encoding: colors and positions start at one → Fin κ and Fin ℓ indexed from zero, allowing ℓ = 0; reason: relabeling preserves all tuples and scores, with the empty tuple as the natural boundary.
--   - encoding: finite guess set with corresponding scores → strictly lexicographically ordered rows with natural feedback pairs; reason: each set with one nonnegative score per guess has exactly one representation, while impossible feedback is rejected by satisfiability and negative scores have no encoding.
--   - encoding: MSP is NP-complete with respect to size ℓ → CookPvsNP.NPComplete on self-delimiting binary encodings of the entire explicit instance; reason: standard machine-based NP membership and many-one hardness require total input length, including every guess and feedback, without a bound on the number of guesses.
-- source:
--   Stuckman and Zhang, arXiv:cs/0512049v1, §2.1, Theorem 2.1, PDF p. 4; https://arxiv.org/abs/cs/0512049v1

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_StuckmanMastermind_NPC_Languages

namespace StuckmanMastermind.NPC

theorem theorem_2_1 :
    CookPvsNP.NPComplete uniformLanguage ∧
    ∀ κ : ℕ, 1 < κ → CookPvsNP.NPComplete (fixedLanguage κ) := by sorry

end StuckmanMastermind.NPC
