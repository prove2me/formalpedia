-- Prove2me | Theorems.Thm_PI_StabSplit_UnipW_sum_W_nonneg
-- name    : PI.StabSplit.UnipW.sum_W_nonneg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:31:07.596301+00:00
-- url     : https://prove2.me/theorems/214ee512-1a30-543a-89ef-4fb29a2c4250
-- title:
--   Unip W: sum W nonneg
-- statement:
--   The Unip W construction uses the sum W nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L134-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L134-L136

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_NilpotentOrthogonalComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.StabSplit PI.StabSplit.UnipW

theorem PI.StabSplit.UnipW.sum_W_nonneg {k r : ℕ} (w : Fin (2 * r + k + 1) → ℂ) :
    0 ≤ ∑ i : Fin (2 * r + k + 1), if (r ≤ i.val ∧ i.val ≤ r + k) then Complex.normSq (w i) else 0 := by sorry
