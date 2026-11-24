-- Prove2me | Theorems.Thm_PI_QnLevBasicsW_Hpk_eq
-- name    : PI.QnLevBasicsW.Hpk_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:08:20.750036+00:00
-- url     : https://prove2.me/theorems/011e19f9-16a4-494b-949f-835c90bf37f4
-- title:
--   Qn Lev Basics W: Hpk eq
-- statement:
--   The Qn Lev Basics W construction uses the Hpk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L147-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L147-L177

import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}

theorem PI.QnLevBasicsW.Hpk_eq :
    Hpk k (i + r') = (fromBlocks (Hpk k r') 0 0 (Jrest k i r')).submatrix (split k i r') (split k i r') := by sorry
