-- Prove2me | Theorems.Thm_PI_FrameInd_herm_mulVec_mulVec
-- name    : PI.FrameInd.herm_mulVec_mulVec
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:39:22.00765+00:00
-- url     : https://prove2.me/theorems/6593be6c-e67a-45da-bcc0-3f95b532d217
-- title:
--   Frame Ind: herm mul Vec mul Vec
-- statement:
--   The Frame Ind construction uses the herm mul Vec mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/FinrankUperpOfDet.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/FinrankUperpOfDet.lean#L13-L16

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_FinrankUperpOfDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.FrameInd

theorem PI.FrameInd.herm_mulVec_mulVec {ι κ : Type*} [Fintype ι] [Fintype κ] (H : Matrix ι ι ℂ) (A : Matrix ι κ ℂ)
    (v w : κ → ℂ) : herm H (A *ᵥ v) (A *ᵥ w) = herm (Aᴴ * H * A) v w := by sorry
