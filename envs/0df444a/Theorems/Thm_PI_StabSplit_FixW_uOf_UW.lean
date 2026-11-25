-- Prove2me | Theorems.Thm_PI_StabSplit_FixW_uOf_UW
-- name    : PI.StabSplit.FixW.uOf_UW
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:38:47.533847+00:00
-- url     : https://prove2.me/theorems/f10d2f5b-6953-43e1-9607-e080b77b0012
-- title:
--   Fix W: u Of UW
-- statement:
--   The Fix W construction uses the u Of UW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/FixSub.lean#L141-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/FixSub.lean#L141-L145

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_FixSub
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
open PI PI.StabSplit PI.StabSplit.FixW

theorem PI.StabSplit.FixW.uOf_UW {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {g : B.Mat k r}
    (hg : g ∈ FixSet k r z) : uOf k r g ∈ UWset k r z := by sorry
