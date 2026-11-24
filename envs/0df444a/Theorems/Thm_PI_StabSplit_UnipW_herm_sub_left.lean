-- Prove2me | Theorems.Thm_PI_StabSplit_UnipW_herm_sub_left
-- name    : PI.StabSplit.UnipW.herm_sub_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:06:25.693909+00:00
-- url     : https://prove2.me/theorems/6b2c85ea-d888-42cb-be82-b47d93ef5418
-- title:
--   Unip W: herm sub left
-- statement:
--   The Unip W construction uses the herm sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L156-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L156-L159

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

theorem PI.StabSplit.UnipW.herm_sub_left {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (a b w : Fin m → ℂ) :
    herm H (a - b) w = herm H a w - herm H b w := by sorry
