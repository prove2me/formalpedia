-- Prove2me | Theorems.Thm_PIQnLT_bvec_lev
-- name    : PIQnLT.bvec_lev
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:17:21.272997+00:00
-- url     : https://prove2.me/theorems/0b6c829d-2907-4122-bcd3-3f6a637dc19d
-- title:
--   PIQn LT: bvec lev
-- statement:
--   The PIQn LT construction uses the bvec lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L70-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L70-L84

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

theorem PIQnLT.bvec_lev (q : Fin (2 * r' + k + 1)) : bvec (levPos k i r' q) = liftVec k i r' (bvec q) := by sorry
