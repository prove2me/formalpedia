-- Prove2me | Theorems.Thm_PI_TOW_fockR_zero_left
-- name    : PI.TOW.fockR_zero_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:06.557331+00:00
-- url     : https://prove2.me/theorems/8251b99c-9857-4f07-be56-c28e1316a60c
-- title:
--   TOW: fock R zero left
-- statement:
--   The TOW construction uses the fock R zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FockLin.lean#L61-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FockLin.lean#L61-L62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW
open PI.TO
variable {σ R : Type*} [CommRing R]

theorem PI.TOW.fockR_zero_left (g : MvPolynomial σ R) : fockR 0 g = 0 := by sorry
