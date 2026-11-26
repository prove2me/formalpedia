-- Prove2me | Theorems.Thm_PalomarZF207_sigma1_sound_consistent
-- name    : PalomarZF207.sigma1_sound_consistent
-- status  : Proved
-- author  : @LG
-- created : 2026-11-21T17:14:53.073453+00:00
-- url     : https://prove2.me/theorems/e99a3610-1b5c-4b57-a2fd-e62f12c233b8
-- title:
--   ZF207: arithmetic $\Sigma_1$-soundness implies consistency
-- statement:
--   Arithmetic $\Sigma_1$-soundness of ZF (the full-class form `ArithmeticSigma1Sound` of Definition 1.1) implies consistency of ZF (`Consistent`). In the source this is `ArithmeticSigma1SoundZF.consistent`, transported to the standalone class by `SigmaBridge`; it is the step that lets the unprovability-of-nonhalting clause apply under the soundness hypothesis in Theorem 1.2(2).
-- source:
--   James Chang, ZF207 paper (2026), Definition 1.1 and proof of Theorem 1.2; production proof https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/ProofSources/Literal207SigmaSoundness.lean#L10-L20 and https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/ProofSources/Independence/SigmaBridge.lean

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_statement

namespace PalomarZF207

theorem sigma1_sound_consistent : ArithmeticSigma1Sound → Consistent := by sorry

end PalomarZF207
