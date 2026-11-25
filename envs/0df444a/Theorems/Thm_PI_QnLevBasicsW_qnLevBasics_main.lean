-- Prove2me | Theorems.Thm_PI_QnLevBasicsW_qnLevBasics_main
-- name    : PI.QnLevBasicsW.qnLevBasics_main
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:47:36.622463+00:00
-- url     : https://prove2.me/theorems/82820abd-32dc-526c-b984-a1ffbe7c0879
-- title:
--   Qn Lev Basics W: qn Lev Basics main
-- statement:
--   The Qn Lev Basics W construction uses the qn Lev Basics main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L210-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L210-L212

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
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

theorem PI.QnLevBasicsW.qnLevBasics_main :
    LevHom ∧ LevUH ∧ LevN ∧ LevUW ∧ LevWb ∧ LevEll := by sorry
