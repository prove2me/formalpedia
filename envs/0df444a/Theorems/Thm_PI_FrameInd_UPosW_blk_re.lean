-- Prove2me | Theorems.Thm_PI_FrameInd_UPosW_blk_re
-- name    : PI.FrameInd.UPosW.blk_re
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:08:20.348276+00:00
-- url     : https://prove2.me/theorems/b5be63fc-aa87-41ed-ac0d-d257d4d3fe37
-- title:
--   UPos W: blk re
-- statement:
--   The UPos W construction uses the blk re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/ColsConjTranspose.lean#L59-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/ColsConjTranspose.lean#L59-L74

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_ColsConjTranspose
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
open PI PI.FrameInd PI.FrameInd.UPosW

theorem PI.FrameInd.UPosW.blk_re {m : ℕ} (a : Fin m → ℂ) :
    (star (Sum.elim (0 : Fin m → ℂ) a) ⬝ᵥ
      (fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0 (-1) *ᵥ Sum.elim (0 : Fin m → ℂ) a)).re =
      -∑ b, Complex.normSq (a b) := by sorry
