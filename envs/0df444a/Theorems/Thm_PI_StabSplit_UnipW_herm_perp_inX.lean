-- Prove2me | Theorems.Thm_PI_StabSplit_UnipW_herm_perp_inX
-- name    : PI.StabSplit.UnipW.herm_perp_inX
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:39:30.39581+00:00
-- url     : https://prove2.me/theorems/6ee29ae6-db6f-5063-9ddf-529f0d3e6a38
-- title:
--   Unip W: herm perp in X
-- statement:
--   The Unip W construction uses the herm perp in X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L87-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L87-L95

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

theorem PI.StabSplit.UnipW.herm_perp_inX {k r : ℕ} {v x : Fin (2 * r + k + 1) → ℂ} (hv : perpX k r v) (hx : inX k r x) :
    herm (Hpk k r) v x = 0 := by sorry
