-- Prove2me | Theorems.Thm_PalomarZF207_halt_unprovable_of_sigma1_sound
-- name    : PalomarZF207.halt_unprovable_of_sigma1_sound
-- status  : Proved
-- author  : @LG
-- created : 2026-11-21T17:14:44.52292+00:00
-- url     : https://prove2.me/theorems/55990749-2379-4199-b25a-f6426240c123
-- title:
--   ZF207: $\Sigma_1$-soundness implies unprovability of halting
-- statement:
--   Let $H$ be any closed set-theoretic sentence that expresses blank-tape halting of the literal 207-state machine in every ZF model (`Represents207 H`). If ZF is arithmetically $\Sigma_1$-sound, then ZF does not prove $H$. This is the halting direction of Theorem 1.2(2), in lemma form generalized over the representing sentence. In the source it follows by proving $H\to H_\Sigma$ for a $\Sigma_1$ halting sentence $H_\Sigma$, applying soundness, and invoking nonhalting under consistency (`literal207_physical_unprovable`).
-- source:
--   James Chang, ZF207 paper (2026), Theorem 1.2(2); production proof https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/ProofSources/Literal207SigmaSoundness.lean#L36-L57 and https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/ProofSources/Independence/Top.lean#L39-L52

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_statement

namespace PalomarZF207

theorem halt_unprovable_of_sigma1_sound (H : Formula) (hH : Represents207 H) : ArithmeticSigma1Sound → ¬ Provable H := by sorry

end PalomarZF207
