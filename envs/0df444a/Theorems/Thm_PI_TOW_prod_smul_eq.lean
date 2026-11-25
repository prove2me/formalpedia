-- Prove2me | Theorems.Thm_PI_TOW_prod_smul_eq
-- name    : PI.TOW.prod_smul_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:01:32.022941+00:00
-- url     : https://prove2.me/theorems/0e8d4a1f-496b-41a8-924e-364c2063b4ee
-- title:
--   TOW: prod smul eq
-- statement:
--   The TOW construction uses the prod smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FilterConcatWLength.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FilterConcatWLength.lean#L31-L33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FilterConcatWLength
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

theorem PI.TOW.prod_smul_eq {σ K : Type*} [CommRing K] {ι : Type*} [Fintype ι] (c : ι → K) (x : ι → MvPolynomial σ K) :
    ∏ i, (c i • x i) = (∏ i, c i) • ∏ i, x i := by sorry
