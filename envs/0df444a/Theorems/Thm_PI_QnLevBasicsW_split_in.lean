-- Prove2me | Theorems.Thm_PI_QnLevBasicsW_split_in
-- name    : PI.QnLevBasicsW.split_in
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:47:39.155983+00:00
-- url     : https://prove2.me/theorems/bb9e4cdd-8176-5935-b6dd-a474db74bea5
-- title:
--   Qn Lev Basics W: split in
-- statement:
--   The Qn Lev Basics W construction uses the split in property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L47-L53

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

theorem PI.QnLevBasicsW.split_in (p : Fin (2 * (i + r') + k + 1)) (a : Fin (2 * r' + k + 1)) (h : p.val = a.val + i) :
    split k i r' p = Sum.inl a := by sorry
