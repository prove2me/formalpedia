-- Prove2me | Theorems.Thm_PI_FrameInd_Vc_mulVec
-- name    : PI.FrameInd.Vc_mulVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:30:52.960709+00:00
-- url     : https://prove2.me/theorems/ff85097e-dc4d-4930-ac24-bdccf7cc7901
-- title:
--   Frame Ind: Vc mul Vec
-- statement:
--   The Frame Ind construction uses the Vc mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/FinrankUperpOfDet.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/FinrankUperpOfDet.lean#L38-L41

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

theorem PI.FrameInd.Vc_mulVec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    Vc k r z z' g *ᵥ c = ∑ i, c i • gramVec k r z z' g i := by sorry
