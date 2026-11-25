-- Prove2me | Theorems.Thm_PI_StabSplit_FixW_unipotent_part_fixes_vector
-- name    : PI.StabSplit.FixW.unipotent_part_fixes_vector
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:06:00.523918+00:00
-- url     : https://prove2.me/theorems/ae28d724-130b-5de0-acd1-333bf7f14ed1
-- title:
--   Fix W: unipotent part fixes vector
-- statement:
--   The Fix W construction uses the unipotent part fixes vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/FixSub.lean#L123-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/FixSub.lean#L123-L139

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

theorem PI.StabSplit.FixW.unipotent_part_fixes_vector {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {g : B.Mat k r}
    (hg : g ∈ FixSet k r z) : uOf k r g *ᵥ z = z := by sorry
