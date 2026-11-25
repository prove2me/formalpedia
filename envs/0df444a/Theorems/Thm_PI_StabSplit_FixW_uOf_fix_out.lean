-- Prove2me | Theorems.Thm_PI_StabSplit_FixW_uOf_fix_out
-- name    : PI.StabSplit.FixW.uOf_fix_out
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:38:35.48998+00:00
-- url     : https://prove2.me/theorems/8f33f353-f288-4157-a3a3-8e41bfd6d681
-- title:
--   Fix W: u Of fix out
-- statement:
--   The Fix W construction uses the u Of fix out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/FixSub.lean#L118-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/FixSub.lean#L118-L121

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

theorem PI.StabSplit.FixW.uOf_fix_out {k r : ℕ} (g : B.Mat k r) (c : Fin (2 * r + k + 1))
    (hc : c.val < r ∨ r + k < c.val) : uOf k r g *ᵥ bvec c = bvec c := by sorry
