-- Prove2me | Theorems.Thm_PIQnLT_posL_lev
-- name    : PIQnLT.posL_lev
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:48:53.134739+00:00
-- url     : https://prove2.me/theorems/445b24d0-aac6-47f1-87c5-ebc0252a1677
-- title:
--   PIQn LT: pos L lev
-- statement:
--   The PIQn LT construction uses the pos L lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L205-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L205-L209

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

theorem PIQnLT.posL_lev (k i r' : ℕ) (j : Fin (mdim k (i + r') ⟨i, by omega⟩)) :
    posL k (i + r') ⟨i, by omega⟩ j = levPos k i r' (posL k r' 0 (Fin.cast (mdim_lev k i r') j)) := by sorry
