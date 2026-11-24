-- Prove2me | Theorems.Thm_PIQnLT_single_lev
-- name    : PIQnLT.single_lev
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:53:33.963344+00:00
-- url     : https://prove2.me/theorems/0f612b0c-6ebf-4dd1-a206-e134baefa70a
-- title:
--   PIQn LT: single lev
-- statement:
--   The PIQn LT construction uses the single lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzConjTranspose.lean#L78-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzConjTranspose.lean#L78-L84

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

theorem PIQnLT.single_lev (a b : Fin (2 * r' + k + 1)) :
    Matrix.single (levPos k i r' a) (levPos k i r' b) (1 : ℂ) = Lz k i r' (Matrix.single a b 1) := by sorry
