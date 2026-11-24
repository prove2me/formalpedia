-- Prove2me | Theorems.Thm_PI_FrameInd_UPosW_cols_conjTranspose
-- name    : PI.FrameInd.UPosW.cols_conjTranspose
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:39:36.875811+00:00
-- url     : https://prove2.me/theorems/48c8fedb-453c-4053-b1db-c1954429b87c
-- title:
--   UPos W: cols conj Transpose
-- statement:
--   The UPos W construction uses the cols conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/ColsConjTranspose.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/ColsConjTranspose.lean#L12-L15

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

theorem PI.FrameInd.UPosW.cols_conjTranspose (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    (cols k r z z' γ)ᴴ = Matrix.of fun i j => star (gramVec k r z z' γ i j) := by sorry
