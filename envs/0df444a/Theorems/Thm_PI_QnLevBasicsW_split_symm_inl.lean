-- Prove2me | Theorems.Thm_PI_QnLevBasicsW_split_symm_inl
-- name    : PI.QnLevBasicsW.split_symm_inl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:07:56.912477+00:00
-- url     : https://prove2.me/theorems/854ded3d-4db0-48ea-8831-e59d169b0034
-- title:
--   Qn Lev Basics W: split symm inl
-- statement:
--   The Qn Lev Basics W construction uses the split symm inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L41-L42

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

theorem PI.QnLevBasicsW.split_symm_inl (a : Fin (2 * r' + k + 1)) :
    ((split k i r').symm (Sum.inl a)).val = a.val + i := by sorry
