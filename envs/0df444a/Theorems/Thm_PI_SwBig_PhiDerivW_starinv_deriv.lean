-- Prove2me | Theorems.Thm_PI_SwBig_PhiDerivW_starinv_deriv
-- name    : PI.SwBig.PhiDerivW.starinv_deriv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:27:41.241013+00:00
-- url     : https://prove2.me/theorems/542d0af5-aa81-5069-9e09-cd41be588d65
-- title:
--   Phi Deriv W: starinv deriv
-- statement:
--   The Phi Deriv W construction uses the starinv deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PhiDerivative/StarinvDeriv.lean#L13-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PhiDerivative/StarinvDeriv.lean#L13-L29

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

theorem PI.SwBig.PhiDerivW.starinv_deriv :
    HasStrictFDerivAt (fun z : ℂ => (star (1 + z))⁻¹) (-(Complex.conjCLE : ℂ →L[ℝ] ℂ)) 0 := by sorry
