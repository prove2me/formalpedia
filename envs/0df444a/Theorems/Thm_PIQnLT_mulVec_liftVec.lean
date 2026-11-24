-- Prove2me | Theorems.Thm_PIQnLT_mulVec_liftVec
-- name    : PIQnLT.mulVec_liftVec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:17:43.103397+00:00
-- url     : https://prove2.me/theorems/af091d2c-ac01-4464-be01-0e8f6e13a590
-- title:
--   PIQn LT: mul Vec lift Vec
-- statement:
--   The PIQn LT construction uses the mul Vec lift Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L18-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L18-L33

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

theorem PIQnLT.mulVec_liftVec (M : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (v : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k i r' M *ᵥ liftVec k i r' v = liftVec k i r' (M *ᵥ v) := by sorry
