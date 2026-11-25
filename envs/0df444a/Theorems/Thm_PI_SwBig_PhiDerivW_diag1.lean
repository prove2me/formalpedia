-- Prove2me | Theorems.Thm_PI_SwBig_PhiDerivW_diag1
-- name    : PI.SwBig.PhiDerivW.diag1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:11.995501+00:00
-- url     : https://prove2.me/theorems/edd29020-f4ea-4f3b-8315-14480bd5b30b
-- title:
--   Phi Deriv W: diag1
-- statement:
--   The Phi Deriv W construction uses the diag1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PhiDerivative/StarinvDeriv.lean#L80-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PhiDerivative/StarinvDeriv.lean#L80-L80

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

theorem PI.SwBig.PhiDerivW.diag1 : Matrix.diagonal (1 : Fin (2 * r + k + 1) → ℂ) = 1 := by sorry
