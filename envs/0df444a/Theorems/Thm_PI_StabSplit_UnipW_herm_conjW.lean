-- Prove2me | Theorems.Thm_PI_StabSplit_UnipW_herm_conjW
-- name    : PI.StabSplit.UnipW.herm_conjW
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:02:14.34137+00:00
-- url     : https://prove2.me/theorems/c36bf2d3-1360-4119-b531-a84f3a1164b4
-- title:
--   Unip W: herm conj W
-- statement:
--   The Unip W construction uses the herm conj W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L111-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L111-L118

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

theorem PI.StabSplit.UnipW.herm_conjW {k r : ℕ} {v w : Fin (2 * r + k + 1) → ℂ} (hv : perpX k r v) (hw : perpX k r w) :
    herm (Hpk k r) w v = star (herm (Hpk k r) v w) := by sorry
