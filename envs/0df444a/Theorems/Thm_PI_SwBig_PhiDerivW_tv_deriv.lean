-- Prove2me | Theorems.Thm_PI_SwBig_PhiDerivW_tv_deriv
-- name    : PI.SwBig.PhiDerivW.tv_deriv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:27:51.214502+00:00
-- url     : https://prove2.me/theorems/1d4a2712-0b84-4112-b76a-66330999de31
-- title:
--   Phi Deriv W: tv deriv
-- statement:
--   The Phi Deriv W construction uses the tv deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PhiDerivative/StarinvDeriv.lean#L47-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PhiDerivative/StarinvDeriv.lean#L47-L67

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

theorem PI.SwBig.PhiDerivW.tv_deriv : HasStrictFDerivAt (fun x : Fin r → ℂ => tv k r (1 + x)) (dvC k r) 0 := by sorry
