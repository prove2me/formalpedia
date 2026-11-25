-- Prove2me | Theorems.Thm_PI_TOW_fockR_zero_right
-- name    : PI.TOW.fockR_zero_right
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:37:20.817142+00:00
-- url     : https://prove2.me/theorems/682fc1c2-adc1-576c-9f71-efe851f5c9a3
-- title:
--   TOW: fock R zero right
-- statement:
--   The TOW construction uses the fock R zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FockLin.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FockLin.lean#L64-L65

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

theorem PI.TOW.fockR_zero_right (f : MvPolynomial σ R) : fockR f 0 = 0 := by sorry
