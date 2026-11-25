-- Prove2me | Theorems.Thm_PI_StabSplit_UnipW_definite
-- name    : PI.StabSplit.UnipW.definite
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:39:37.6232+00:00
-- url     : https://prove2.me/theorems/e24263ed-b0c1-51b1-8653-b20545dcfaaa
-- title:
--   Unip W: definite
-- statement:
--   The Unip W construction uses the definite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L167-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L167-L202

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

theorem PI.StabSplit.UnipW.definite {k r : ℕ} {y z : Fin (2 * r + k + 1) → ℂ} (hy : perpX k r y) (hz : inWb k r z)
    (hT : 0 < Tz k r z) (h1 : herm (Hpk k r) y y = 0) (h2 : herm (Hpk k r) y z = 0) : inX k r y := by sorry
