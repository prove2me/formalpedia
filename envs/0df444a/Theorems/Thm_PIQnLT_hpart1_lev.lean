-- Prove2me | Theorems.Thm_PIQnLT_hpart1_lev
-- name    : PIQnLT.hpart1_lev
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:48:17.582869+00:00
-- url     : https://prove2.me/theorems/a26199b3-b5a8-40fe-ad4e-b47eab2ab71f
-- title:
--   PIQn LT: hpart1 lev
-- statement:
--   The PIQn LT construction uses the hpart1 lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzConjTranspose.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzConjTranspose.lean#L89-L93

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

theorem PIQnLT.hpart1_lev (a b : Fin (2 * r' + k + 1)) :
    hpart1 (Hpk k (i + r')) (Matrix.single (levPos k i r' a) (levPos k i r' b) 1) =
      Lz k i r' (hpart1 (Hpk k r') (Matrix.single a b 1)) := by sorry
