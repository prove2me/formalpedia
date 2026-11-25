-- Prove2me | Theorems.Thm_PI_SwBig_PhiDerivW_diagC_apply
-- name    : PI.SwBig.PhiDerivW.diagC_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:31:34.030331+00:00
-- url     : https://prove2.me/theorems/967455c0-56b9-5a8f-9dbe-dda0e56c2586
-- title:
--   Phi Deriv W: diag C apply
-- statement:
--   The Phi Deriv W construction uses the diag C apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PhiDerivative/StarinvDeriv.lean#L72-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PhiDerivative/StarinvDeriv.lean#L72-L73

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PhiDerivative_StarinvDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SwBig PI.SwBig.PhiDerivW
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable (k r : ℕ)

theorem PI.SwBig.PhiDerivW.diagC_apply (v : Fin (2 * r + k + 1) → ℂ) : diagC k r v = Matrix.diagonal v := by sorry
