-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_jm_jm_mul
-- name    : PI.UnitaryGroupMassFormula.DSIC.jm_jm_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:38:52.026316+00:00
-- url     : https://prove2.me/theorems/ce2e4825-55f3-46f8-b66c-d72e7013344e
-- title:
--   DSIC: jm jm mul
-- statement:
--   The DSIC construction uses the jm jm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CentralCharacters/AdjointEquivalence.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CentralCharacters/AdjointEquivalence.lean#L18-L20

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QdetMemAdjSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_AdjointEquivalence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DSIC
open PI.DSInfCharCap
open scoped InnerProductSpace Matrix

theorem PI.UnitaryGroupMassFormula.DSIC.jm_jm_mul {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := by sorry
