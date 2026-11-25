-- Prove2me | Theorems.Thm_PI_CharIdemW_end_one_ne_zero
-- name    : PI.CharIdemW.end_one_ne_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:44:24.479394+00:00
-- url     : https://prove2.me/theorems/5a38f437-9326-4d53-9135-c6061cc5d119
-- title:
--   Char Idem W: end one ne zero
-- statement:
--   The Char Idem W construction uses the end one ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/Scalar.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/Scalar.lean#L46-L51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open PI PI.CharIdemW
open PI.CharIdem
variable {G : Type} [Group G] [Fintype G]

theorem PI.CharIdemW.end_one_ne_zero (W : FDRep ℂ G) [Simple W] : (1 : Module.End ℂ W) ≠ 0 := by sorry
