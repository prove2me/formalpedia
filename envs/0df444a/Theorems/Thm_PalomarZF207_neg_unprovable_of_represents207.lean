-- Prove2me | Theorems.Thm_PalomarZF207_neg_unprovable_of_represents207
-- name    : PalomarZF207.neg_unprovable_of_represents207
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T17:14:34.220845+00:00
-- url     : https://prove2.me/theorems/4d4a92a8-65ed-4dc9-83c0-8712a4bcaa5f
-- title:
--   ZF207: consistency implies unprovability of nonhalting
-- statement:
--   Let $H$ be any closed set-theoretic sentence that expresses blank-tape halting of the literal 207-state machine in every ZF model (`Represents207 H`). If ZF is consistent, then ZF does not prove $\neg H$. This is the unprovability clause of Theorem 1.2(1), in lemma form generalized over the representing sentence (the paper states it for the sentence it constructs). In the source it follows from the calibration principle (Lemma 1.3) and Gödel's second incompleteness theorem for the calibrated arithmetic theory, via `neg_unprovable_of_calibration`.
-- source:
--   James Chang, ZF207 paper (2026), Theorem 1.2(1) and Lemma 1.3 (lem:calib); production proof https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/ProofSources/Independence/Godel.lean#L24-L40 and https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/ProofSources/Independence/Top.lean#L39-L52

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_statement

namespace PalomarZF207

theorem neg_unprovable_of_represents207 (H : Formula) (hH : Represents207 H) : Consistent → ¬ Provable (Neg H) := by sorry

end PalomarZF207
