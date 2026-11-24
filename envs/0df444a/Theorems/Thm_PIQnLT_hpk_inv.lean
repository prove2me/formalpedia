-- Prove2me | Theorems.Thm_PIQnLT_hpk_inv
-- name    : PIQnLT.hpk_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:55:29.516219+00:00
-- url     : https://prove2.me/theorems/d6006f6a-881f-4cf7-99a6-d05a1250e650
-- title:
--   PIQn LT: hpk inv
-- statement:
--   The PIQn LT construction uses the hpk inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzConjTranspose.lean#L86-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzConjTranspose.lean#L86-L87

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

theorem PIQnLT.hpk_inv (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r := by sorry
