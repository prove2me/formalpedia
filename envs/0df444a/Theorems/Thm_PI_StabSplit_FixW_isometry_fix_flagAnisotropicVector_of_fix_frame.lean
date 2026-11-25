-- Prove2me | Theorems.Thm_PI_StabSplit_FixW_isometry_fix_flagAnisotropicVector_of_fix_frame
-- name    : PI.StabSplit.FixW.isometry_fix_flagAnisotropicVector_of_fix_frame
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:38:32.859839+00:00
-- url     : https://prove2.me/theorems/9b1fb42c-a6d5-43a9-8789-d6c05674d6ca
-- title:
--   Fix W: isometry fix flag Anisotropic Vector of fix frame
-- statement:
--   The Fix W construction uses the isometry fix flag Anisotropic Vector of fix frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/FixSub.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/FixSub.lean#L57-L60

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

theorem PI.StabSplit.FixW.isometry_fix_flagAnisotropicVector_of_fix_frame {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z) :
    g *ᵥ z = z := by sorry
