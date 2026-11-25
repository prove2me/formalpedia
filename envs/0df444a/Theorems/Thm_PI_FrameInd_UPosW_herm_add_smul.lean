-- Prove2me | Theorems.Thm_PI_FrameInd_UPosW_herm_add_smul
-- name    : PI.FrameInd.UPosW.herm_add_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:30:17.351181+00:00
-- url     : https://prove2.me/theorems/f98d5ece-d108-5b47-b44a-1bc498fb0145
-- title:
--   UPos W: herm add smul
-- statement:
--   The UPos W construction uses the herm add smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/ColsConjTranspose.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/ColsConjTranspose.lean#L51-L57

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

theorem PI.FrameInd.UPosW.herm_add_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (w v : Fin n → ℂ) (t : ℂ)
    (h1 : herm H v w = 0) (h2 : herm H w v = 0) :
    herm H (w + t • v) (w + t • v) = herm H w w + (star t * t) * herm H v v := by sorry
