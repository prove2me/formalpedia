-- Prove2me | Theorems.Thm_PI_ET_HornW_psum_eq
-- name    : PI.ET.HornW.psum_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:20.163316+00:00
-- url     : https://prove2.me/theorems/73c560bd-5aa4-4d77-88b7-982ec00453cf
-- title:
--   Horn W: psum eq
-- statement:
--   The Horn W construction uses the psum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L99-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L99-L112

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

theorem PI.ET.HornW.psum_eq {k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    psum f k = ∑ i : Fin k, f (Fin.castLE hk i) := by sorry
