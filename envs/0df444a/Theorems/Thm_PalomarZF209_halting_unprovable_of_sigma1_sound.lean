-- Prove2me | Theorems.Thm_PalomarZF209_halting_unprovable_of_sigma1_sound
-- name    : PalomarZF209.halting_unprovable_of_sigma1_sound
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T18:37:55.600721+00:00
-- url     : https://prove2.me/theorems/714552c0-d5ad-4748-9367-316f3298a9d1
-- title:
--   ZF209: Sigma_1-soundness implies ZF cannot prove halting
-- statement:
--   There is a closed sentence $H$ representing the machine's blank-tape halting in every $\mathrm{ZF}$ model such that, if $\mathrm{ZF}$ is arithmetically $\Sigma_1$-sound, then $\mathrm{ZF}$ does not prove $H$.
--   $$\exists H,\ \mathrm{Represents209}(H)\wedge\bigl(\mathrm{ArithmeticSigma1Sound}\to\neg\,\mathrm{Provable}(H)\bigr).$$
--   This is the halting-unprovability direction of the main theorem under the stronger arithmetic $\Sigma_1$-soundness hypothesis. Together with the nonhalting direction (which needs only consistency), it yields full independence of the halting sentence.
--
--   **Formalization Note** `ArithmeticSigma1Sound` quantifies over closed $\Sigma_1$ arithmetic sentences represented in $\mathrm{ZF}$'s natural numbers; the source converts it to the production soundness hypothesis via a $\Sigma_1$ bridge.
-- source:
--   https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF209/paper/zf209.tex (Theorem 1.2(2), thm:main); proof: https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF209/ProofSources/Literal209SigmaSoundness.lean and https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF209/ProofSources/Independence/Top.lean

import Definitions.Def_PalomarZF209_History
import Definitions.Def_PalomarZF209_SetTheory
import Definitions.Def_PalomarZF209_Arithmetic

namespace PalomarZF209
theorem halting_unprovable_of_sigma1_sound : ∃ H : Formula, Represents209 H ∧ (ArithmeticSigma1Sound → ¬ Provable H) := by sorry
end PalomarZF209
