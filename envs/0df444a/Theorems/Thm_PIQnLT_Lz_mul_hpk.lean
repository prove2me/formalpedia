-- Prove2me | Theorems.Thm_PIQnLT_Lz_mul_hpk
-- name    : PIQnLT.Lz_mul_hpk
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:55:37.225774+00:00
-- url     : https://prove2.me/theorems/1f2552d1-842b-4b12-b3d8-916765b031ab
-- title:
--   PIQn LT: Lz mul hpk
-- statement:
--   The PIQn LT construction uses the Lz mul hpk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzConjTranspose.lean#L61-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzConjTranspose.lean#L61-L70

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_ExpLz
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
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

theorem PIQnLT.Lz_mul_hpk (W : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Lz k i r' W * Hpk k (i + r') = Lz k i r' (W * Hpk k r') := by sorry
