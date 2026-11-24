-- Prove2me | Theorems.Thm_PIQnLT_isUnit_det_of_UH
-- name    : PIQnLT.isUnit_det_of_UH
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:17:19.174957+00:00
-- url     : https://prove2.me/theorems/4ccf5b4c-7c04-4ae0-9617-b84e625c0ba6
-- title:
--   PIQn LT: is Unit det of UH
-- statement:
--   The PIQn LT construction uses the is Unit det of UH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L106-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L106-L111

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_SecondCapelliMinorLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PIQnLT
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k i r' : ℕ}

theorem PIQnLT.isUnit_det_of_UH (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (hg : g ∈ UH (Hpk k r')) :
    IsUnit g.det := by sorry
