-- Prove2me | Theorems.Thm_PI_ET_HornW_norm_det_diag_exp
-- name    : PI.ET.HornW.norm_det_diag_exp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:48.446296+00:00
-- url     : https://prove2.me/theorems/def881a9-0cc2-4fb6-baf8-bf28417c9920
-- title:
--   Horn W: norm det diag exp
-- statement:
--   The Horn W construction uses the norm det diag exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L118-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L118-L123

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

theorem PI.ET.HornW.norm_det_diag_exp {k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    ‖(diagonal (fun i : Fin k => (Real.exp (2 * f (Fin.castLE hk i)) : ℂ))).det‖ =
      Real.exp (2 * psum f k) := by sorry
