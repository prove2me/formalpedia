-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QnFFZero_nset_uh
-- name    : PI.UnitaryGroupMassFormula.QnFFZero.nset_uh
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:50:58.774796+00:00
-- url     : https://prove2.me/theorems/53989923-a449-46ed-a2b5-44ec62c5ce6c
-- title:
--   Qn FFZero: nset uh
-- statement:
--   The Qn FFZero construction uses the nset uh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelGeneralLinear/GlevZero.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroLevelGeneralLinear/GlevZero.lean#L22-L24

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

theorem PI.UnitaryGroupMassFormula.QnFFZero.nset_uh (k r : ℕ) (n : Mx k r) (h : n ∈ Nset k r) : n ∈ UH (Hpk k r) := by sorry
