-- Prove2me | Theorems.Thm_PI_ET_HornW_prod_exp_eq
-- name    : PI.ET.HornW.prod_exp_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:50.159733+00:00
-- url     : https://prove2.me/theorems/612cf244-a5de-57de-88a5-d0b58fe545ad
-- title:
--   Horn W: prod exp eq
-- statement:
--   The Horn W construction uses the prod exp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L125-L127

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped MatrixOrder ComplexOrder
noncomputable section
open PI PI.ET
open PI.ET.HornW
variable {n : ℕ}

theorem PI.ET.HornW.prod_exp_eq {k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    ∏ i : Fin k, Real.exp (2 * f (Fin.castLE hk i)) = Real.exp (2 * psum f k) := by sorry
