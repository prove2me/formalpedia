-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QnFFZero_glev_zero
-- name    : PI.UnitaryGroupMassFormula.QnFFZero.glev_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:50:40.760867+00:00
-- url     : https://prove2.me/theorems/1f5e2bdc-c7f5-4403-bf49-3148ccb06c7a
-- title:
--   Qn FFZero: glev zero
-- statement:
--   The Qn FFZero construction uses the glev zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelGeneralLinear/GlevZero.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelGeneralLinear/GlevZero.lean#L14-L20

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelGeneralLinear_GlevZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QnFFZero
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem PI.UnitaryGroupMassFormula.QnFFZero.glev_zero (k r : ℕ) (g : Mx k r) : g ∈ Glev k r 0 ↔ g ∈ UH (Hpk k r) := by sorry
