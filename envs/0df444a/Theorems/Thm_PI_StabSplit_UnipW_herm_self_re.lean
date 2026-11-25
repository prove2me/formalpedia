-- Prove2me | Theorems.Thm_PI_StabSplit_UnipW_herm_self_re
-- name    : PI.StabSplit.UnipW.herm_self_re
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:38:37.963614+00:00
-- url     : https://prove2.me/theorems/9afd7827-3645-41d3-8dbd-1187705136aa
-- title:
--   Unip W: herm self re
-- statement:
--   The Unip W construction uses the herm self re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L120-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L120-L132

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

theorem PI.StabSplit.UnipW.herm_self_re {k r : ℕ} {w : Fin (2 * r + k + 1) → ℂ} (hw : perpX k r w) (hL : w (Lk k r) = 0) :
    (herm (Hpk k r) w w).re =
      ∑ i, if (r ≤ i.val ∧ i.val ≤ r + k) then Complex.normSq (w i) else 0 := by sorry
