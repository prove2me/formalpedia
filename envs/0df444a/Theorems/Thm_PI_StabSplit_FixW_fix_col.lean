-- Prove2me | Theorems.Thm_PI_StabSplit_FixW_fix_col
-- name    : PI.StabSplit.FixW.fix_col
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:17:12.570405+00:00
-- url     : https://prove2.me/theorems/186a8af0-c217-4bf7-9fc7-b0f4de8b3a08
-- title:
--   Fix W: fix col
-- statement:
--   The Fix W construction uses the fix col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/FixSub.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/FixSub.lean#L49-L55

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

theorem PI.StabSplit.FixW.fix_col {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ FixSet k r z)
    (j : Fin (2 * r + k + 1)) (hj : j.val < r) (i : Fin (2 * r + k + 1)) :
    g i j = if i = j then 1 else 0 := by sorry
