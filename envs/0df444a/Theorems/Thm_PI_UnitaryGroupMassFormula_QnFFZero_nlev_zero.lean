-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QnFFZero_nlev_zero
-- name    : PI.UnitaryGroupMassFormula.QnFFZero.nlev_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:41:29.194215+00:00
-- url     : https://prove2.me/theorems/1cf00488-5720-54d3-aa5c-f96526f11b1d
-- title:
--   Qn FFZero: nlev zero
-- statement:
--   The Qn FFZero construction uses the nlev zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelGeneralLinear/GlevZero.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelGeneralLinear/GlevZero.lean#L26-L32

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

theorem PI.UnitaryGroupMassFormula.QnFFZero.nlev_zero (k r : ℕ) (n : Mx k r) : n ∈ Nlev k r 0 ↔ n ∈ Nset k r := by sorry
