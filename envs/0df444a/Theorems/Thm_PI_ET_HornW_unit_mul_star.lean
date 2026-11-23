-- Prove2me | Theorems.Thm_PI_ET_HornW_unit_mul_star
-- name    : PI.ET.HornW.unit_mul_star
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:33.313797+00:00
-- url     : https://prove2.me/theorems/e0414cbb-8f38-4c81-bd1d-5fe927a46add
-- title:
--   Horn W: unit mul star
-- statement:
--   The Horn W construction uses the unit mul star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L20-L22

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

theorem PI.ET.HornW.unit_mul_star {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) :
    W * Wᴴ = 1 := by sorry
