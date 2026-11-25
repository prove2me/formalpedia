-- Prove2me | Theorems.Thm_PI_FrameInd_CountsW_blockA_re
-- name    : PI.FrameInd.CountsW.blockA_re
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:30:46.464866+00:00
-- url     : https://prove2.me/theorems/0de8c4f5-aeb6-5169-8c9b-06da9363a73b
-- title:
--   Counts W: block A re
-- statement:
--   The Counts W construction uses the block A re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/Counts.lean#L50-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/Counts.lean#L50-L61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NonposCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_Counts
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
open PI PI.FrameInd PI.FrameInd.CountsW
open PI.FrameInd

theorem PI.FrameInd.CountsW.blockA_re (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hz : inWb k r z)
    (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) (hc : ∀ b, c (Sum.inr b) = 0) :
    (herm (gramM k r z z' γ) c c).re =
      (herm (Hpk k r) z z).re * Complex.normSq (c (Sum.inl (Fin.last r))) := by sorry
