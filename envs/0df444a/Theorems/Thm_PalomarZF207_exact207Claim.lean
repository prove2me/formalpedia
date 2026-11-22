-- Prove2me | Theorems.Thm_PalomarZF207_exact207Claim
-- name    : PalomarZF207.exact207Claim
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T17:15:04.517969+00:00
-- url     : https://prove2.me/theorems/66647b73-c38b-444d-992b-e4668147d19f
-- title:
--   Exact 207-state claim: a ZF halting sentence with conditional independence
-- statement:
--   Theorem 1.2 of Chang's ZF207 paper, in the exact standalone form checked by the source repository's statement comparator. There is a closed sentence $H$ of the language of set theory such that:
--
--   - **Meaning.** In every model $(V,E)$ of ZF — including models with nonstandard natural numbers — and under every assignment, $H$ holds exactly when $V$ contains an internally finite halting history of the literal 207-state machine from the blank tape (`Represents207 H`).
--   - **Unprovability of nonhalting.** If ZF is consistent (`Consistent`), then ZF does not prove $\neg H$.
--   - **Independence under soundness.** If ZF is arithmetically $\Sigma_1$-sound (`ArithmeticSigma1Sound`, the full-class form of Definition 1.1), then ZF proves neither $H$ nor $\neg H$.
--
--   The machine-meaning clause and the compiler correctness behind it are conclusions, not assumptions: the sentence must be constructed and its meaning proved in every ZF model. The source repository proves this claim in Lean 4.35.0 (`PalomarZF207.exact207Claim`, via `ZF207.Halting.exact207Claim`); the present target is the same statement against the standalone definitions, to be proved in the mission environment. The external nonhalting clause of Theorem 1.2(1) is proved separately in the source and is not part of this exact statement.
-- source:
--   James Chang, 'Nonhalting and ZF-independence for a 207-state Turing machine' (2026), Theorem 1.2 (thm:main), https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/paper/zf207.tex; statement https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/ProofSources/Challenge.lean#L536-L543; proof entry https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/ProofSources/Solution.lean#L8 and https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/ProofSources/Halting/Final.lean

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_statement

namespace PalomarZF207

theorem exact207Claim : Exact207Claim := by sorry

end PalomarZF207
