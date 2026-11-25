-- Prove2me | Theorems.Thm_PI_SwBig_PhiDerivW_main
-- name    : PI.SwBig.PhiDerivW.main
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:31:28.793866+00:00
-- url     : https://prove2.me/theorems/bf333709-c989-5e5d-a866-d0ae563ed7ab
-- title:
--   Phi Deriv W: main
-- statement:
--   The Phi Deriv W construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PhiDerivative/StarinvDeriv.lean#L82-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PhiDerivative/StarinvDeriv.lean#L82-L112

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

theorem PI.SwBig.PhiDerivW.main (hW : LongWeylElementSquare) :
    HasStrictFDerivAt
      (fun p : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r => Phi k r p.1 p.2.1 p.2.2.1 p.2.2.2)
      (Lm k r) 0 := by sorry
