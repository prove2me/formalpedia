-- Prove2me | Theorems.Thm_PI_QnLevBasicsW_split_symm_inr
-- name    : PI.QnLevBasicsW.split_symm_inr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:08:16.183851+00:00
-- url     : https://prove2.me/theorems/c847fd71-0b2f-48a4-8a8f-71b7bd64083f
-- title:
--   Qn Lev Basics W: split symm inr
-- statement:
--   The Qn Lev Basics W construction uses the split symm inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L44-L45

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

theorem PI.QnLevBasicsW.split_symm_inr (b : Fin (2 * i)) :
    ((split k i r').symm (Sum.inr b)).val = if b.val < i then b.val else b.val + (2 * r' + k + 1) := by sorry
