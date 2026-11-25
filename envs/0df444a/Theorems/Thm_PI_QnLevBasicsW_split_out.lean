-- Prove2me | Theorems.Thm_PI_QnLevBasicsW_split_out
-- name    : PI.QnLevBasicsW.split_out
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:59:56.935858+00:00
-- url     : https://prove2.me/theorems/e01f33cb-4b85-4dae-997b-61ebce44899d
-- title:
--   Qn Lev Basics W: split out
-- statement:
--   The Qn Lev Basics W construction uses the split out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L55-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L55-L64

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

theorem PI.QnLevBasicsW.split_out (p : Fin (2 * (i + r') + k + 1)) (h : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) :
    ∃ b, split k i r' p = Sum.inr b := by sorry
