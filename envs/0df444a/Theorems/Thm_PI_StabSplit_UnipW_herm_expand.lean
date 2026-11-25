-- Prove2me | Theorems.Thm_PI_StabSplit_UnipW_herm_expand
-- name    : PI.StabSplit.UnipW.herm_expand
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:39:08.401599+00:00
-- url     : https://prove2.me/theorems/946f7e6c-c39c-56d9-a6dc-cb2aae9b5ce7
-- title:
--   Unip W: herm expand
-- statement:
--   The Unip W construction uses the herm expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L138-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L138-L144

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

theorem PI.StabSplit.UnipW.herm_expand {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (y z : Fin m → ℂ) (c : ℂ) :
    herm H (y - c • z) (y - c • z) =
      herm H y y - star c * herm H y z - c * herm H z y + c * star c * herm H z z := by sorry
