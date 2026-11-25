-- Prove2me | Theorems.Thm_PI_FrameInd_submatrix_conj
-- name    : PI.FrameInd.submatrix_conj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:31:48.39289+00:00
-- url     : https://prove2.me/theorems/9f8ea870-58f3-4f25-bc58-faf57f6c7eae
-- title:
--   Frame Ind: submatrix conj
-- statement:
--   The Frame Ind construction uses the submatrix conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/QBuild.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/QBuild.lean#L10-L13

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_Counts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegativeBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_QBuild
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

theorem PI.FrameInd.submatrix_conj {ι κ : Type*} [Fintype ι] [Fintype κ] (W M : Matrix ι ι ℂ) (e : κ ≃ ι) :
    (W.submatrix id e)ᴴ * M * W.submatrix id e = (Wᴴ * M * W).submatrix e e := by sorry
