-- Prove2me | Theorems.Thm_PI_StabSplit_UnipW_herm_inv
-- name    : PI.StabSplit.UnipW.herm_inv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:57:42.098486+00:00
-- url     : https://prove2.me/theorems/9beeb087-e67b-4695-966a-96fe775da04a
-- title:
--   Unip W: herm inv
-- statement:
--   The Unip W construction uses the herm inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L161-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L161-L165

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

theorem PI.StabSplit.UnipW.herm_inv {m : ℕ} {H g : Matrix (Fin m) (Fin m) ℂ} (hg : gᴴ * H * g = H) (v w : Fin m → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by sorry
