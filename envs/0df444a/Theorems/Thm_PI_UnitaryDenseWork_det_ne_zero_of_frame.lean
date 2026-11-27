-- Prove2me | Theorems.Thm_PI_UnitaryDenseWork_det_ne_zero_of_frame
-- name    : PI.UnitaryDenseWork.det_ne_zero_of_frame
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:48:17.753273+00:00
-- url     : https://prove2.me/theorems/3c7d2097-9ed4-4c36-b2b6-667e598a4500
-- title:
--   Unitary Dense Work: det ne zero of frame
-- statement:
--   The Unitary Dense Work construction uses the det ne zero of frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryDensity/Derived.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryDensity/Derived.lean#L12-L17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_Derived
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexOrder
open PI PI.UnitaryDenseWork

theorem PI.UnitaryDenseWork.det_ne_zero_of_frame {n : ℕ} (G y : Matrix (Fin n) (Fin n) ℂ) (hy : yᴴ * G * y = 1) :
    y.det ≠ 0 := by sorry
