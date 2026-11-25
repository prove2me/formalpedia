-- Prove2me | Theorems.Thm_PIQnLT_hpk_mulVec_liftVec
-- name    : PIQnLT.hpk_mulVec_liftVec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:47:54.21487+00:00
-- url     : https://prove2.me/theorems/c2ec7fec-50b6-437e-b603-fe308de567b4
-- title:
--   PIQn LT: hpk mul Vec lift Vec
-- statement:
--   The PIQn LT construction uses the hpk mul Vec lift Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L35-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L35-L55

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

theorem PIQnLT.hpk_mulVec_liftVec (v : Fin (2 * r' + k + 1) → ℂ) :
    Hpk k (i + r') *ᵥ liftVec k i r' v = liftVec k i r' (Hpk k r' *ᵥ v) := by sorry
